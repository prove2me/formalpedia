-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventUniverseQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.eventUniverseQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:48:16.681696+00:00
-- url     : https://prove2.me/theorems/295b2c47-fd9f-4170-a8f5-18fe4d5e48b2
-- title:
--   BDL26 Random Perturbation: event Universe Query value
-- statement:
--   The counted finite construction supplies exactly the order used in actual resampling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L76-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L76-L101

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventUniverseQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    (eventUniverseQuery P J hr).1 = (Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r) := by sorry
