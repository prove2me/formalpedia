-- Prove2me | Theorems.Thm_ProbabilityTheory_levyTruncationSeq_spec
-- name    : ProbabilityTheory.levyTruncationSeq_spec
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:26:54.104634+00:00
-- url     : https://prove2.me/theorems/0454b203-fbb5-4df3-b43b-5acef3518b12
-- title:
--   LeanLevy: ProbabilityTheory.levyTruncationSeq_spec
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L860

import Init
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}

theorem ProbabilityTheory.levyTruncationSeq_spec (hν : IsLevyMeasure ν) :
    StrictMono (levyTruncationSeq hν) ∧
    ∀ j : ℕ, (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by sorry
