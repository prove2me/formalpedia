-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.eventQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:12:55.339859+00:00
-- url     : https://prove2.me/theorems/6a71242d-d76c-4c51-aab3-1894365037d3
-- title:
--   BDL26 Random Perturbation: event Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the event Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L64-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean#L64-L71

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set

theorem QEC.Coding.BDL26RandomPerturbation.eventQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    (p : eventSupport P J radius e → Space) :
    (eventQuery P J radius lambda K e p).1 = true ↔ p ∈ eventBad P J radius lambda K e := by sorry
