-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventCompareQuery_priority_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_priority_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:49:25.738079+00:00
-- url     : https://prove2.me/theorems/6629446a-7d4d-4613-899a-09e82a04b8d8
-- title:
--   BDL26 Random Perturbation: event Compare Query priority correct
-- statement:
--   The BDL26 Random Perturbation construction uses the event Compare Query priority correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L64-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L64-L66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_priority_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : (eventCompareQuery P J r e f).1 = true ↔ eventPriorityLE P J r e f := by sorry
