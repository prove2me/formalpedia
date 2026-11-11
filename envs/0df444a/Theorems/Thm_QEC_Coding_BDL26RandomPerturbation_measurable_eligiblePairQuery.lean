-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_eligiblePairQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_eligiblePairQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:03:52.233067+00:00
-- url     : https://prove2.me/theorems/20974f3e-f41d-4775-bad3-83405e4ea662
-- title:
--   BDL26 Random Perturbation: measurable eligible Pair Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable eligible Pair Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L142-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L142-L147

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_eligiblePairQuery (P : TannerSquarePresentation) (r : ℝ)
    (a b : Triangle P) :
    Measurable (fun J : Vertex P → Space => eligiblePairQuery P J r a b) := by sorry
