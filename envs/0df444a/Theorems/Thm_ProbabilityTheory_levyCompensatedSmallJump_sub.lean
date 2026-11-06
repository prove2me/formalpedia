-- Prove2me | Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJump_sub
-- name    : ProbabilityTheory.levyCompensatedSmallJump_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:12:30.437977+00:00
-- url     : https://prove2.me/theorems/7ab338fc-40d0-4888-ac68-441870ced013
-- title:
--   LeanLevy source dependency: levyCompensatedSmallJump_sub
-- statement:
--   Exact original LeanLevy source theorem promoted as a private dependency of the jump-path law and process construction.

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Probability_Poisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic
open ProbabilityTheory
/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/

/-!
# Time-indexed Poisson random measures

Specialize the abstract Poisson random measure to the product space `ℝ × E`, with `ℝ` read as time
and `E` as the mark space, under the product intensity `volume.prod m`. The evaluation on a
space-time band `(s, t] × A` is the number of realized marks in `A` occurring during the time
window `(s, t]`; the running count `poissonTimeCount K X A t` is its value on the initial window
`(0, t]`.

## Main definitions

* `ProbabilityTheory.poissonTimeCount` — the running count of realized points in `(0, t] × A`.
* `ProbabilityTheory.levyCompensatedSmallJump` — the compensated small-jump integral of a Lévy
  measure at time `t`, as an element of `L²(μ)`.

## Main results

* `ProbabilityTheory.measurable_poissonTimeCount` — the running count is a measurable function of the
  sample point.
* `ProbabilityTheory.map_poissonRandomMeasure_band` — the count in a band `(s, t] × A` is Poisson with
  mean `(t - s) · m A`.
* `ProbabilityTheory.map_poissonTimeCount` — the running count `poissonTimeCount K X A t` is Poisson
  with mean `t · m A`.
* `ProbabilityTheory.poissonTimeCount_add` — the running count is pathwise additive over consecutive
  time windows.
* `ProbabilityTheory.iIndepFun_poissonRandomMeasure_bands` — **independent increments**: the counts
  over consecutive disjoint time bands are mutually independent.
* `ProbabilityTheory.memLp_two_smallJumpFun` — the small-jump test function is square-integrable
  against `volume.prod ν` for any Lévy measure `ν`.
* `ProbabilityTheory.memLp_two_smallJumpBandFun` — the same for the band test function supported on a
  time window `(s, t]`.
* `ProbabilityTheory.levyCompensatedSmallJump_sub` — the increment of the compensated small-jump
  integral over `(s, t]` is the compensated integral of the band test function.
* `ProbabilityTheory.integral_levyCompensatedSmallJump` — the compensated small-jump integral has
  mean zero.
* `ProbabilityTheory.eLpNorm_sq_levyCompensatedSmallJump` — **Campbell's isometry**: its second
  moment is `t · ∫_{(-1,1)} x² dν`.
* `ProbabilityTheory.map_levyLargeJumpCount` — the number of large jumps up to time `t` is Poisson
  with mean `t · ν {x | 1 ≤ |x|}`.
* `ProbabilityTheory.levyLargeJumpSum` — the sum of the jump sizes of the realized marks in the band
  `(0, t] × {x | 1 ≤ |x|}`, as a series of piece sums.
* `ProbabilityTheory.measurable_levyLargeJumpSum` — the large-jump sum is a measurable function of the
  sample point.
* `ProbabilityTheory.levyLargeJumpSum_ae_eq_integral` — almost surely the large-jump sum is the
  Bochner integral of the jump size against the random measure over the band.
* `ProbabilityTheory.integral_levyLargeJumpSum` — **Campbell's formula**: under a first moment on the
  large jumps, the mean of the large-jump sum is `t · ∫_{|x|≥1} x dν`.
* `ProbabilityTheory.levyLargeJumpSum_ae_eq_toReal_sub` — the large-jump sum as a difference of
  Lebesgue integrals of the positive and negative jump parts.
* `ProbabilityTheory.charFun_map_levyLargeJumpSum` — **the large-jump sum is compound Poisson**: its
  characteristic function is `exp (t · ∫_{|x|≥1} (e^{iξx} − 1) dν)`.
* `ProbabilityTheory.charFun_map_compensatedBandSum` — the compensated Poisson sum of the band test
  function on a mark set `A ⊆ (-1, 1)` of finite `ν`-mass has characteristic function
  `exp (t · ∫_A (e^{ixξ} − 1 − ixξ) dν)`.
* `ProbabilityTheory.charFun_map_levyCompensatedSmallJump` — **the law of the compensated small-jump
  integral**: its characteristic function is `exp (t · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)`, the
  small-jump factor of the Lévy–Khintchine exponent.
* `ProbabilityTheory.charFun_map_levyLargeJumpSum_sub`,
  `ProbabilityTheory.charFun_map_levyCompensatedSmallJump_sub` — **the increment laws over a time band
  `(s, t]`**: the large-jump increment is compound Poisson and the compensated small-jump increment
  carries the small-jump factor, both at rate `(t − s)`.

Every statement is read off the abstract superposition and disjoint-family independence laws of
`poissonRandomMeasure` on `ℝ × E`; the band mass factorizes as `volume (Ioc s t) * m A` through
`Measure.prod_prod`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal


variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω} {A : Set E} {s t : ℝ}



















/-! ### The compensated small-jump integral of a Lévy measure

Specializing the mark space to `E = ℝ` and the intensity to `volume.prod ν` for a **Lévy measure**
`ν`, the small-jump test function `1_{(0,t] × (-1,1)}(s, x) · x` is square-integrable, so its
compensated Poisson integral `levyCompensatedSmallJump` is a genuine `L²(μ)` random variable. It
has mean zero and second moment `t · ∫_{(-1,1)} x² dν` (Campbell's isometry). The number of large
jumps up to time `t` is Poisson with mean `t · ν {|x| ≥ 1}`. -/


variable {ν : Measure ℝ} [SigmaFinite ν] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}

theorem ProbabilityTheory.levyCompensatedSmallJump_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {s t : ℝ}
    (h0 : 0 ≤ s) (hst : s ≤ t) :
    levyCompensatedSmallJump hd hν t - levyCompensatedSmallJump hd hν s
      = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp _) := by sorry
