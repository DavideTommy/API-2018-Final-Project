#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//Variable Chunk Size
#define CHUNK_SIZE 7

/**
 * Turing machine
 * Prototipo di Turing Machine NON DETERMINISTICA a nastro singolo
 * @author Davide
 */

/**
 * Global values
*/

//Aceptance variables
int unknown = 0;
int notAccepted = 0;

/**
 * parser, acceptance, global variables
 */
char* smallBuffer;
long maxStep = 0;
int* acceptanceStatus;
int numberAcceptanceStatus = -1;

typedef struct Transition {
    int inState;
    char read;
    char write;
    char move;
    int outState;
} transitions;

size_t higherTransitionInStatus = 0;
int numberTotalTransitions = -1;
int* transitionsCounter;
transitions* inputTransitions;
transitions*** hashMap;

//Input tape
char* inputTape;
size_t tapeLength = 0;
size_t totalChunk = 0;

//struct MT
typedef struct TuringMachines {
    size_t currentMaxChunk;
    size_t machineTapeLength;
    long currentStep;
    int tapeHead;
    char* tape;
    int son;
    transitions* transition;
    struct TuringMachines* next;
    struct TuringMachines* previous;
} turingMachine;

int activeMachines = 0;

// input
int result = -1;
turingMachine* toDelete;

transitions fakeTransition;
turingMachine* currentExecutingMachine;


int nextFound = 0;

//Only for not determinism
turingMachine* fatherMachine = NULL;
int fatherTransition;

turingMachine* tail = NULL;
turingMachine* head = NULL;

turingMachine* prevCurrent = NULL;

turingMachine* firstSonCreated = NULL;
turingMachine* lastSonCreated = NULL;

int totalSonCreated = 0;

/**
 * Creates Pointers HshMap
 * Map is ordered by InputState
 */
static inline void hashMapCreator(){

    int inHashMapTmp = 0;

    transitionsCounter = calloc((size_t) higherTransitionInStatus + 1, sizeof(int));
    hashMap = malloc((higherTransitionInStatus + 1) * sizeof(struct transitions***));

    for (int j = 0; j <= higherTransitionInStatus ; j++) {
        hashMap[j] = malloc(sizeof(struct Transition**));
    }

    for (int i = 0; i <= numberTotalTransitions ; i++) {            // <= perchè parto da -1 a contare
        inHashMapTmp = inputTransitions[i].inState;
        (transitionsCounter[inHashMapTmp])++;
        hashMap[inHashMapTmp] = realloc(hashMap[inHashMapTmp], transitionsCounter[inHashMapTmp] * sizeof(struct transition**));
        hashMap[inHashMapTmp][transitionsCounter[inHashMapTmp] - 1] = &inputTransitions[i];
    }
}

/**
 * Not Malloc MT Prototype
 */
void beginner() {

    activeMachines++;

    head = malloc(sizeof(turingMachine));


    head->tape = malloc((CHUNK_SIZE) * sizeof(char));
    memcpy(head->tape, &inputTape[0], CHUNK_SIZE);

    fakeTransition.outState = 0;
    fakeTransition.read = head->tape[0];
    fakeTransition.write = '\0';
    fakeTransition.move = '\0';
    fakeTransition.inState = 0;

    head->currentMaxChunk = 1;
    head->son = 0;
    head->currentStep = 0;
    head->tapeHead = 0;
    head->machineTapeLength = CHUNK_SIZE;
    head->transition = &fakeTransition;
    head->previous = NULL;
    head->next = NULL;

    tail = head;
}

/**
 * Pulisce tutto a fine nastro prima di eseguire il nastro nuovo (non so se sia completa, avendo una SEGFAULT non so se
 * ho leak lost da valgrind
 */
static inline void endTapeCleaner(){

    result = -1;

    //tape
    free(inputTape);
    tapeLength = 0;
    totalChunk = 0;

    //machines
    activeMachines = 0;
    nextFound = 0;

    //other values
    unknown = 0;
    notAccepted = 0;

    tail = NULL;
    head = NULL;
    firstSonCreated = NULL;
    fatherMachine = NULL;
    nextFound = 0;
    currentExecutingMachine = NULL;
    toDelete = NULL;
}

/**
 * Final Cleaner
 * At the end of the execution of a tape reset all variables and free unused memory
 */
static inline void finalCleaner() {

    free(smallBuffer);

    //tr
    higherTransitionInStatus = 0;
    numberTotalTransitions = -1;
    free(inputTransitions);
    free(transitionsCounter);

    //acc
    free(acceptanceStatus);
    numberAcceptanceStatus = -1;


    //free the hashmap
    for (int i = 0; i < higherTransitionInStatus; i++) {
        free(hashMap[i]);
    }
    free(hashMap);
}

/**
 * Machine eraser
 */

static  inline void machineEraser(){
    activeMachines--;

    // 4 casi: testa, coda, sia testa che coda, né testa né coda, me la gioco coi previous e next
    if (currentExecutingMachine == head){
        if (head->next == NULL) {
            if (totalSonCreated == 0) {
                head = NULL;
                tail = NULL;
            }
            else if (totalSonCreated != 0){
                head = firstSonCreated;
                tail = lastSonCreated;
            }
        }
        else if (head->next != NULL) {
            head->next->previous = NULL;
            head = head->next;
        }
    }

    else if (currentExecutingMachine == tail) {
        tail->previous->next = NULL;
        tail = tail->previous;
    }

    else if (currentExecutingMachine != tail && currentExecutingMachine != head){
        if (currentExecutingMachine->son == 1){
            if(currentExecutingMachine == lastSonCreated->next){
                lastSonCreated->next = NULL;
            }
        }
        else if (currentExecutingMachine->son == 0) {
            currentExecutingMachine->next->previous = currentExecutingMachine->previous;
            currentExecutingMachine->previous->next = currentExecutingMachine->next;
        }
    }

    free(currentExecutingMachine->tape);
    toDelete = currentExecutingMachine;
}

/**
 * Unknown verifier 
 * Verifies if machine goes in loop or passes the max step
 */

static inline int unknownVerifier() {

    if(currentExecutingMachine->currentStep == maxStep || (currentExecutingMachine->transition->read == currentExecutingMachine->transition->write && currentExecutingMachine->transition->move == 'S' && currentExecutingMachine->transition->inState == currentExecutingMachine->transition->outState) || (currentExecutingMachine->transition->read == '_' && currentExecutingMachine->transition->write == 'Q' && currentExecutingMachine->transition->move != 'S')) {
        unknown++;
        machineEraser();
        currentExecutingMachine = currentExecutingMachine->next;
        free(toDelete);
        toDelete = NULL;
        return 1;
    }
    else {
        currentExecutingMachine->son = 0;
        prevCurrent = currentExecutingMachine;
        currentExecutingMachine = currentExecutingMachine->next;
        return 0;
    }
}
/**
 * Core of the machine: overwrite the character, move the head on the tape and verifies if the next step is 1,0,U
 */
static inline void run() {

    //sovrascrivo la testa
    currentExecutingMachine->tape[currentExecutingMachine->tapeHead] = currentExecutingMachine->transition->write;

    if(currentExecutingMachine->transition->move == 'R') {
        currentExecutingMachine->tapeHead++;

        if(currentExecutingMachine->tapeHead >= (currentExecutingMachine->machineTapeLength)) {

            currentExecutingMachine->machineTapeLength = currentExecutingMachine->machineTapeLength + CHUNK_SIZE;
            currentExecutingMachine->tape = realloc(currentExecutingMachine->tape, currentExecutingMachine->machineTapeLength);

            if(currentExecutingMachine->currentMaxChunk < totalChunk) {
                memcpy(&currentExecutingMachine->tape[currentExecutingMachine->tapeHead], &inputTape[(currentExecutingMachine->currentMaxChunk) * CHUNK_SIZE], CHUNK_SIZE);
                currentExecutingMachine->currentMaxChunk++;
            }

            else {
                memset(&currentExecutingMachine->tape[currentExecutingMachine->tapeHead], '_', CHUNK_SIZE);
            }
        }
    }


    else if (currentExecutingMachine->transition->move == 'L'){

        if (currentExecutingMachine->tapeHead == 0) {
            currentExecutingMachine->machineTapeLength = currentExecutingMachine->machineTapeLength + CHUNK_SIZE;
            currentExecutingMachine->tape = realloc(currentExecutingMachine->tape, currentExecutingMachine->machineTapeLength);
            currentExecutingMachine->tapeHead = currentExecutingMachine->tapeHead + CHUNK_SIZE;
            memmove(&currentExecutingMachine->tape[CHUNK_SIZE], &currentExecutingMachine->tape[0], currentExecutingMachine->machineTapeLength - CHUNK_SIZE);
            memset(&currentExecutingMachine->tape[0], '_', CHUNK_SIZE);
        }

        currentExecutingMachine->tapeHead--;
    }

    currentExecutingMachine->currentStep++;
}

/**
 * Prendo la macchina corrente OK
 * se non accetta cerco linearmente le transizioni successive contandole e basta (salvo la prima in un pointer) OK
 * Controllo a runtime se le trTrovate per caso accettano OK
 * finito il ciclo verifico che next found non sia 0, nel caso quitto (da scrivere una machineDeleter) OK
 * altrimenti: se next found == 1 copio la tr salvata dentro al padre e faccio la move OK
 * altrimenti: se next Found => 1: faccio un for (nextFound > 0 poi dentro if (i = 1) copia la prima
 * tr nel padre, else prendi lastSonAllocated (in cui il primo del mega while corrisponderà con assPointer
 * e alloca una tr dopo dentro questo else, if i == 2 firstSon allocated = questa macchina
 * finisco di salvare le tr e di creare eventuali nuove macchine
 * ora le devo eseguire tutte: while(currentMachine == NULL)
 * faccio run del padre
 * current machine.next = firstSon allocated
 * quando esco dal while e ho valutato le macchine executing machine = executing machine.fatherTr.next *
 */

static inline int manager(){

    while (activeMachines > 0) {

        currentExecutingMachine = head;

        while(currentExecutingMachine != NULL) {

            fatherTransition = currentExecutingMachine->transition->outState;

            for (int i = 0; i < transitionsCounter[fatherTransition] ; i++) {

                if(hashMap[fatherTransition][i]->read == currentExecutingMachine->tape[currentExecutingMachine->tapeHead]){
                    nextFound++;

                    for (int j = 0; j <= numberAcceptanceStatus; j++) {
                        if(hashMap[fatherTransition][i]->outState == acceptanceStatus[j]){
                            return 1;
                        }
                    }

                    if(nextFound == 1) {
                        currentExecutingMachine->transition = hashMap[fatherTransition][i];
                    }
                }
            }

            //No valid transition
            if(nextFound == 0){
                notAccepted++;

                machineEraser();

                currentExecutingMachine = currentExecutingMachine->next;
                free(toDelete);
                toDelete = NULL;
            }

                //Deterministic
            else if (nextFound == 1){
                run();
                unknownVerifier();
            }

            //Not Deterministic chase
            else if (nextFound > 1) {

                fatherMachine = currentExecutingMachine;

                //before I create and execute sons, so the father is the same, after I do COW on the father
                for (int i = 0; i < transitionsCounter[fatherTransition] ; i++) {

                    if(hashMap[fatherTransition][i]->read == fatherMachine->tape[fatherMachine->tapeHead]) {

                        //il padre non lo duplico in questa maniera: se é il primo figlio in assoluto
                        if(totalSonCreated == 0 && hashMap[fatherTransition][i] != fatherMachine->transition) {

                            firstSonCreated = malloc(sizeof(turingMachine));
                            currentExecutingMachine = firstSonCreated;

                            firstSonCreated->currentMaxChunk = fatherMachine->currentMaxChunk;
                            firstSonCreated->machineTapeLength = fatherMachine->machineTapeLength;
                            firstSonCreated->currentStep = fatherMachine->currentStep;
                            firstSonCreated->tapeHead = fatherMachine->tapeHead;
                            firstSonCreated->transition = hashMap[fatherTransition][i];
                            firstSonCreated->next = NULL;
                            firstSonCreated->previous = NULL;

                            firstSonCreated->son = 1;

                            firstSonCreated->tape = malloc(firstSonCreated->machineTapeLength * sizeof(char));
                            memcpy(firstSonCreated->tape, fatherMachine->tape, firstSonCreated->machineTapeLength);

                            run();

                            if (unknownVerifier() == 0){
                                totalSonCreated++;
                                lastSonCreated = firstSonCreated;
                            }
                            else {
                                firstSonCreated = NULL;
                            }
                        }

                        else if(totalSonCreated > 0 && hashMap[fatherTransition][i] != fatherMachine->transition) {

                            lastSonCreated->next = malloc(sizeof(turingMachine));

                            lastSonCreated->next->currentMaxChunk = fatherMachine->currentMaxChunk;
                            lastSonCreated->next->machineTapeLength = fatherMachine->machineTapeLength;
                            lastSonCreated->next->currentStep = fatherMachine->currentStep;
                            lastSonCreated->next->tapeHead = fatherMachine->tapeHead;
                            lastSonCreated->next->next = NULL;
                            lastSonCreated->next->transition = hashMap[fatherTransition][i];
                            lastSonCreated->next->son = 1;
                            lastSonCreated->next->previous = lastSonCreated;

                            lastSonCreated->next->tape = malloc(lastSonCreated->next->machineTapeLength * sizeof(char));
                            memcpy(lastSonCreated->next->tape, fatherMachine->tape,lastSonCreated->next->machineTapeLength);

                            currentExecutingMachine = lastSonCreated->next;

                            run();

                            if (unknownVerifier() == 0){
                                totalSonCreated++;
                                lastSonCreated = prevCurrent;

                            }
                        }
                    }
                }

                //Eseguo il padre, cosí il nastro originale é stato copiato giusto ai figli
                currentExecutingMachine = fatherMachine;

                run();
                unknownVerifier();
            }

            //passo alla macchina successiva
            nextFound = 0;
        }

        //when I've exausted father list
        if(firstSonCreated != NULL){
            tail->next = firstSonCreated;
            firstSonCreated->previous = tail;
            tail = lastSonCreated;
        }
        activeMachines = activeMachines + totalSonCreated;
        totalSonCreated = 0;
        firstSonCreated = NULL;

    }
    //se non ho più macchine attive posso essere solo che a 0 o a U (e le valuto dopo)
    return 0;
}

int main() {

    /**
     * Global parser initializations
     */

    inputTransitions = malloc(sizeof(transitions));

    char *bigBuffer;

    int inTmp = -1;
    char readTmp = '\0';
    char writeTmp = '\0';
    char moveTmp = '\0';
    int outTmp = -1;

    /**
     * Parser zone
     */

    scanf("%ms", &smallBuffer);
    if (strcmp(smallBuffer, "tr\n") != 0) {

        while (scanf("%d %c %c %c %d", &inTmp, &readTmp, &writeTmp, &moveTmp, &outTmp)) {
            numberTotalTransitions++;

            inputTransitions = realloc(inputTransitions, (numberTotalTransitions + 1) * sizeof(transitions));

            inputTransitions[numberTotalTransitions].inState = inTmp;
            inputTransitions[numberTotalTransitions].read = readTmp;
            inputTransitions[numberTotalTransitions].write = writeTmp;
            inputTransitions[numberTotalTransitions].move = moveTmp;
            inputTransitions[numberTotalTransitions].outState = outTmp;

            if (inTmp > higherTransitionInStatus)
                higherTransitionInStatus = (size_t) inTmp;
        }
    }
    free(smallBuffer);
    hashMapCreator();

    /**
     * Saving acceptance status
     */
    scanf("%ms", &smallBuffer);
    if (strcmp(smallBuffer, "acc\n") != 0) {
        acceptanceStatus = malloc(sizeof(int));
        int accTmp = -1;

        while (scanf("%d", &accTmp)) {
            numberAcceptanceStatus++;
            acceptanceStatus = realloc(acceptanceStatus, (numberAcceptanceStatus + 1) * sizeof(int));
            acceptanceStatus[numberAcceptanceStatus] = accTmp;
        }
    }
    free(smallBuffer);

    /**
     * Saving max step
     */
    scanf("%ms", &smallBuffer);
    if (strcmp(smallBuffer, "max\n") != 0) {
        scanf("%ld", &maxStep);
    }

    /**
    * reading Tapes
    */

    scanf("%s", smallBuffer);
    if (strcmp(smallBuffer, "run\n") != 0) {

        while (scanf("%ms", &bigBuffer) == 1) {
            size_t tmpTapeLenght = 0;
            tmpTapeLenght = strlen(bigBuffer);

            if (tmpTapeLenght % CHUNK_SIZE != 0) {
                totalChunk = ((tmpTapeLenght / CHUNK_SIZE) + 1);
                tapeLength = totalChunk * CHUNK_SIZE;
                inputTape = malloc(tapeLength * sizeof(char));
                memset(inputTape, '_', tapeLength);
                memcpy(inputTape, bigBuffer, tmpTapeLenght);
            } else if (tapeLength % CHUNK_SIZE == 0) {
                totalChunk = (tmpTapeLenght / CHUNK_SIZE);
                tapeLength = tmpTapeLenght;
                inputTape = malloc(tapeLength * sizeof(char));
                memcpy(inputTape, bigBuffer, tapeLength);
            }

            free(bigBuffer);

            beginner();

            //Printing Tapes
            result = manager();

            if (result == 1) {
                printf("%d\n", 1);
                if (totalSonCreated > 0){
                    tail->next = firstSonCreated;
                    tail = lastSonCreated;
                }
                currentExecutingMachine = head;
                while (currentExecutingMachine != NULL){
                    toDelete = currentExecutingMachine;
                    currentExecutingMachine = currentExecutingMachine->next;
                    free(toDelete->tape);
                    free(toDelete);
                }

            } else if (result == 0 && unknown > 0) {
                printf("U\n");
            } else if (result == 0 && unknown == 0 && notAccepted > 0) {
                printf("%d\n", 0);
            }

            endTapeCleaner();
        }
    }
    finalCleaner();
}
