-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dedupQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.dedupQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:00.722117+00:00
-- url     : https://prove2.me/theorems/0c74ca18-9ec6-4cee-a711-61868833e18c
-- title:
--   BDL26 Random Perturbation: dedup Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the dedup Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L43-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L43-L61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.dedupQuery_value {A : Type*} [DecidableEq A] (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (L : List A) :
    (dedupQuery eq L).1 = L.dedup := by sorry
