-- Prove2me | Theorems.Thm_Turing_MultiTapeTM_exists_exact_sequential_replay
-- name    : Turing.MultiTapeTM.exists_exact_sequential_replay
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:23:25.331588+00:00
-- url     : https://prove2.me/theorems/85aaaaee-8d8a-422a-b33c-4bef5a18107b
-- title:
--   Exact replay checkpoints on a deterministic multitape machine
-- statement:
--   A finite-control deterministic multitape machine can be wrapped by a finite-control machine with two banks of the original number of work tapes and the same alphabet. The new machine starts from blank work tapes and has empty public output at every finite cutoff. If the worker first halts at time $t$ with shifted input-head position $p$, write $u$ for the natural subtraction of one from $p$, plus two. The wrapper first halts at time $2t+u$. For every time $j$ in the second run, the checkpoint at $t+u+j$ has the worker's first-run final work tapes on the left, the worker's time-$j$ tapes on the right, and the worker's time-$j$ input-head position. Both banks preserve their corresponding work-tape head positions.
-- source:
--   Verified construction using the rewind-input combinator of the Cslib deterministic multitape machine model.

import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic

open Turing Turing.MultiTapeTM

theorem Turing.MultiTapeTM.exists_exact_sequential_replay {k : ℕ} {Symbol : Type*} {State Summary : Type}
    [Finite State] [Finite Summary] [DecidableEq Summary]
    (worker : MultiTapeTM k Symbol State) (seed : Summary)
    (observe : Summary → Symbol → Summary) (failure : Symbol) :
    ∃ (R : Type) (_finite : Finite R) (replay : MultiTapeTM (k+k) Symbol R),
      ∀ input : List Symbol,
        (∀ t, (replay.runFrom (replay.initCfg input) t).output = []) ∧
        ∀ t, worker.HaltsAt (worker.initCfg input) t →
          let left := worker.runFrom (worker.initCfg input) t
          let rewind := left.inputPos.val - 1 + 2
          replay.HaltsAt (replay.initCfg input) (t+rewind+t) ∧
          ∀ j,
            let right := worker.runFrom (worker.initCfg input) j
            let physical := replay.runFrom (replay.initCfg input) (t+rewind+j)
            physical.inputPos = right.inputPos ∧
            ∀ i : Fin k,
              physical.workTapes (Fin.castAdd k i) = left.workTapes i ∧
              physical.workTapePos (Fin.castAdd k i) = left.workTapePos i ∧
              physical.workTapes (Fin.natAdd k i) = right.workTapes i ∧
              physical.workTapePos (Fin.natAdd k i) = right.workTapePos i := by sorry
