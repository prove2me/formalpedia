-- Prove2me | Theorems.Thm_Turing_SubsequentialTransducer_tm2_polytime
-- name    : Turing.SubsequentialTransducer.tm2_polytime
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:47:21.057879+00:00
-- url     : https://prove2.me/theorems/d36ce0cb-9b5d-4e63-ba97-142608a8c936
-- title:
--   Subsequential finite-state transducers admit polynomial-time TM2 implementations
-- statement:
--   For a fixed subsequential transducer over finite input and output alphabets, there is a polynomial-time Mathlib TM2 that reads its input word and writes the same output word. On each input letter the transducer changes state and emits a word, and when its input ends it emits one final word.
-- source:
--   Mehryar Mohri, Finite-State Transducers in Language and Speech Processing, Computational Linguistics 23(2), 1997, p. 272, https://aclanthology.org/J97-2003/. The transducer linear-time observation is implemented in the Mathlib TM2 stack-machine model.

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_Turing_SubsequentialTransducer_run

namespace Turing.SubsequentialTransducer

theorem tm2_polytime {A B S : Type} [Fintype A] [Fintype B] [Fintype S] [Inhabited B]
    (step : S → A → S × List B) (finish : S → List B) (initial : S) :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List A → List A) (id : List B → List B)
      (run step finish initial)) := by sorry

end Turing.SubsequentialTransducer
