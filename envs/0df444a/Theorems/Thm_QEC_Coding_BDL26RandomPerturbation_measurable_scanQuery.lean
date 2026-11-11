-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_scanQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_scanQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:07:42.854985+00:00
-- url     : https://prove2.me/theorems/2081882f-8744-4547-b80f-6e4b0481e05e
-- title:
--   BDL26 Random Perturbation: measurable scan Query
-- statement:
--   The original first-true scan is measurable with its final clean-scan cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L114-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L114-L127

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_scanQuery {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace (Option A)]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (scanQuery q L) := by sorry
