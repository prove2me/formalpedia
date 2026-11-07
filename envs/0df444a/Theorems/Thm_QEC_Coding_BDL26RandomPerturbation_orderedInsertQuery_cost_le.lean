-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_orderedInsertQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:52:55.598408+00:00
-- url     : https://prove2.me/theorems/d77d5310-e200-4e90-abdb-927940946f30
-- title:
--   BDL26 Random Perturbation: ordered Insert Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the ordered Insert Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L70-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean#L70-L79

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_cost_le {A : Type*} (cmp : A → A → Bool × ℕ) (C : ℕ)
    (hc : ∀ a b, (cmp a b).2 ≤ C) (a : A) (L : List A) :
    (orderedInsertQuery cmp a L).2 ≤ (L.length+1)*(C+1) := by sorry
