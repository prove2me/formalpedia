-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_memberQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.memberQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:19:52.281669+00:00
-- url     : https://prove2.me/theorems/1f292a3e-87d9-489c-a80d-08d43679c9d9
-- title:
--   BDL26 Random Perturbation: member Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the member Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L27-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L27-L35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.memberQuery_cost_le {A : Type*} (eq : A → A → Bool × ℕ) (C : ℕ)
    (h : ∀ a b, (eq a b).2 ≤ C) (a : A) (L : List A) :
    (memberQuery eq a L).2 ≤ L.length*(C+1) := by sorry
