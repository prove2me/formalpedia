-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_listAllQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.listAllQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:01:58.884201+00:00
-- url     : https://prove2.me/theorems/bd5f4200-1f6d-4a9c-a32f-d73129b42ed7
-- title:
--   BDL26 Random Perturbation: list All Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the list All Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L34-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L34-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set

theorem QEC.Coding.BDL26RandomPerturbation.listAllQuery_cost_le {A : Type*} (q : A → Bool × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (listAllQuery q L).2 ≤ L.length*(C+1) := by sorry
