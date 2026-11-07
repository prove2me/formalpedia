-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_indexQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.indexQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:16.990801+00:00
-- url     : https://prove2.me/theorems/e7a3158f-b0cf-4f89-a435-b8216d8689c8
-- title:
--   BDL26 Random Perturbation: index Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the index Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L24-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L24-L29

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.indexQuery_cost_le {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (indexQuery a L).2 ≤ L.length := by sorry
