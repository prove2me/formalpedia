-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_in_triangleInputTuples
-- name    : QEC.Coding.BDL26RandomPerturbation.event_in_triangleInputTuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:48:24.205433+00:00
-- url     : https://prove2.me/theorems/411a2e11-7544-42a0-84c8-7d481b24e6da
-- title:
--   BDL26 Random Perturbation: event in triangle Input Tuples
-- statement:
--   Input rank labels enumerate all eligible four-triangle events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L11-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventUniverse.lean#L11-L21

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.event_in_triangleInputTuples (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) :
    ∃ L ∈ fourTuples (triangleInputList P), L.toFinset = e.val := by sorry
