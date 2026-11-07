-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dedupQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.dedupQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:42:37.543418+00:00
-- url     : https://prove2.me/theorems/ccd96665-77bd-4a5c-a2d5-822ef2b74f61
-- title:
--   BDL26 Random Perturbation: dedup Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the dedup Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L63-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L63-L77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.dedupQuery_cost_le {A : Type*} [DecidableEq A] (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (C : ℕ)
    (hc : ∀ a b, (eq a b).2 ≤ C) (L : List A) :
    (dedupQuery eq L).2 ≤ (L.length+1)^2*(C+1) := by sorry
