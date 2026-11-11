-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_eligibleListQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_eligibleListQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:05:45.007331+00:00
-- url     : https://prove2.me/theorems/867b4fbc-d38c-497e-87b5-12516fba69d4
-- title:
--   BDL26 Random Perturbation: measurable eligible List Query
-- statement:
--   Erasing only the fixed finite-set field retains the original eligibility cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L150-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L150-L160

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_eligibleListQuery (P : TannerSquarePresentation) (r : ℝ)
    (L : List (Triangle P)) :
    Measurable (fun J : Vertex P → Space =>
      ((eligibleListQuery P J r L).1.2, (eligibleListQuery P J r L).2)) := by sorry
