-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_anchorCloseQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_anchorCloseQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:38:10.54193+00:00
-- url     : https://prove2.me/theorems/57d3b35f-9031-4f5c-b6ff-cf1c00fc39ca
-- title:
--   BDL26 Random Perturbation: measurable anchor Close Query
-- statement:
--   Incoming geometry may vary: this includes the arithmetic branch costs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L130-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L130-L140

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.measurable_anchorCloseQuery (P : TannerSquarePresentation) (r : ℝ)
    (a b : Triangle P) :
    Measurable (fun J : Vertex P → Space => anchorCloseQuery P J r a b) := by sorry
