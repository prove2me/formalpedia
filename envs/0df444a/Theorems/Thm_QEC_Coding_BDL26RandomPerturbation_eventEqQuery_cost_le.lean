-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventEqQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventEqQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:50:42.072818+00:00
-- url     : https://prove2.me/theorems/28ebe478-0bab-4e2c-9d2b-4a06f5c0dbc9
-- title:
--   BDL26 Random Perturbation: event Eq Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the event Eq Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L56-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L56-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventEqQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    (eventEqQuery P J r e f).2 ≤ 16*(Fintype.card (Triangle P)+1)+219 := by sorry
