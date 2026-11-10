-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_listAllQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.listAllQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:03:03.975648+00:00
-- url     : https://prove2.me/theorems/4ada6088-3a59-419b-b1d2-dfbc6066b91d
-- title:
--   BDL26 Random Perturbation: list All Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the list All Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L22-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L22-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set

theorem QEC.Coding.BDL26RandomPerturbation.listAllQuery_correct {A : Type*} (q : A → Bool × ℕ) (L : List A) :
    (listAllQuery q L).1 = true ↔ ∀ a ∈ L, (q a).1 = true := by sorry
