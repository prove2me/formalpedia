-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventEqQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.eventEqQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:48:33.37871+00:00
-- url     : https://prove2.me/theorems/c3431dff-9e19-4a01-8783-9e87229fef7b
-- title:
--   BDL26 Random Perturbation: event Eq Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the event Eq Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L47-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L47-L54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventEqQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : (eventEqQuery P J r e f).1 = true ↔ e = f := by sorry
