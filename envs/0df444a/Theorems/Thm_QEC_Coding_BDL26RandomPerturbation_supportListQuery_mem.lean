-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supportListQuery_mem
-- name    : QEC.Coding.BDL26RandomPerturbation.supportListQuery_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:51:52.646165+00:00
-- url     : https://prove2.me/theorems/64177b37-d840-4d4c-a4e0-fd2b9ac48748
-- title:
--   BDL26 Random Perturbation: support List Query mem
-- statement:
--   Refreshes visit the support extracted from the four actual triangle labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L46-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L46-L68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.supportListQuery_mem (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) (v : Vertex P) :
    v ∈ (supportListQuery P J r e).1 ↔ v ∈ eventSupport P J r e := by sorry
