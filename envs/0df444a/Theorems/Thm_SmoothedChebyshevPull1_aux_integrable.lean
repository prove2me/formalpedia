-- Prove2me | Theorems.Thm_SmoothedChebyshevPull1_aux_integrable
-- name    : SmoothedChebyshevPull1_aux_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:39:37.924173+00:00
-- url     : https://prove2.me/theorems/83674adb-307e-4df4-91b9-6b38f0d0a5b1
-- title:
--   Integrability of the smoothed Chebyshev integrand on vertical lines $\mathrm{Re}(s) = \sigma_0 \in (1, 2]$
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$, nonnegative on $(0, \infty)$, supported in $[1/2, 2]$, of multiplicative mass one; fix $\epsilon \in (0,1)$, $X > 3$, and an abscissa $\sigma_0$ with $1 < \sigma_0 \le 2$. The *smoothed Chebyshev integrand* is the function
--
--   $$s \;\longmapsto\; -\frac{\zeta'}{\zeta}(s)\; \mathcal{M}\big(\widetilde{1_\epsilon}\big)(s)\; X^{s},$$
--
--   where $\widetilde{1_\epsilon}$ is the smoothed cutoff built from $F$ and $\mathcal{M}$ the Mellin transform.
--
--   The theorem asserts that this integrand is integrable along the vertical line $\mathrm{Re}(s) = \sigma_0$: the function $t \mapsto -\tfrac{\zeta'}{\zeta}(\sigma_0 + it)\, \mathcal{M}(\widetilde{1_\epsilon})(\sigma_0 + it)\, X^{\sigma_0 + it}$ is integrable on $\mathbb{R}$ (with respect to Lebesgue measure).
--
--   Integrability holds because $|\zeta'/\zeta|$ is uniformly bounded on the line $\mathrm{Re}(s) = \sigma_0 > 1$ (by the absolutely convergent Dirichlet series $\sum \Lambda(n) n^{-\sigma_0}$), $|X^s| = X^{\sigma_0}$ is constant, and the Mellin factor decays in $t$. This justifies both the definition of $\psi_\epsilon(X)$ as a line integral and the vertical-tail bookkeeping in the contour-pulling arguments.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L756-L816

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by sorry
