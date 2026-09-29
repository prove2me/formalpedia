-- Prove2me | Theorems.Thm_SmoothedChebyshevPull2
-- name    : SmoothedChebyshevPull2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:07:13.140493+00:00
-- url     : https://prove2.me/theorems/1bcc5303-6307-4845-b9d0-24a5d263debb
-- title:
--   Second contour pull: splitting the line $\mathrm{Re}(s) = \sigma_1$ around a deeper excursion to $\mathrm{Re}(s) = \sigma_2$
-- statement:
--   Continue the contour-deformation analysis of the smoothed Chebyshev function. Let $F$ be a smoothing kernel of class $C^1$, nonnegative on $(0, \infty)$, supported in $[1/2, 2]$, of multiplicative mass one; fix $\epsilon \in (0, 1)$, $X > 3$, a height $T > 3$, and abscissas $0 < \sigma_2 < \sigma_1 < 1$. Assume $\zeta'/\zeta$ is holomorphic on the punctured box $[\sigma_1, 2] \times i[-T, T] \setminus \{1\}$, and that the full smoothed Chebyshev integrand $-\tfrac{\zeta'}{\zeta}(s)\,\mathcal{M}(\widetilde{1_\epsilon})(s)\,X^s$ is holomorphic on the smaller punctured box $[\sigma_2, 2] \times i[-3, 3] \setminus \{1\}$.
--
--   Then the truncated vertical integral $I_{37}$ along $\mathrm{Re}(s) = \sigma_1$, $|\mathrm{Im}(s)| \le T$, decomposes as
--
--   $$I_{37} \;=\; I_3 - I_4 + I_5 + I_6 + I_7,$$
--
--   where $I_3$ and $I_7$ are the portions of the line $\mathrm{Re}(s) = \sigma_1$ with $3 \le |\mathrm{Im}(s)| \le T$, $I_4$ and $I_6$ are short horizontal segments at heights $\mp 3$ connecting $\sigma_1$ to $\sigma_2$, and $I_5$ is the vertical segment on the deeper line $\mathrm{Re}(s) = \sigma_2$ with $|\mathrm{Im}(s)| \le 3$.
--
--   This second application of Cauchy's theorem pushes the low-height part of the contour (where the zero-free region is widest) further left, to $\mathrm{Re}(s) = \sigma_2$; no new residue appears because the excursion box avoids $s = 1$'s pole contribution, already extracted in the first pull. The decomposition sets up the final estimates: each of $I_3, \dots, I_7$ is exponentially or polynomially small, yielding the error term of the medium-strength Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L1057-L1238

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

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by sorry
