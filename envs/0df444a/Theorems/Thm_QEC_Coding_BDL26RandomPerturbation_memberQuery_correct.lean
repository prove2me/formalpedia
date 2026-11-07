-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_memberQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.memberQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:19:49.097193+00:00
-- url     : https://prove2.me/theorems/f140bc61-8e73-41b8-a660-1301bd291b49
-- title:
--   BDL26 Random Perturbation: member Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the member Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L14-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean#L14-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.memberQuery_correct {A : Type*} (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (a : A) (L : List A) :
    (memberQuery eq a L).1 = true ↔ a ∈ L := by sorry
