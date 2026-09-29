-- Prove2me | Theorems.Thm_SmoothedChebyshevClose_aux
-- name    : SmoothedChebyshevClose_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:01:40.462009+00:00
-- url     : https://prove2.me/theorems/6b7378c1-51fc-4216-92b1-b7485dddbbfd
-- title:
--   Explicit-constant comparison of the smoothed von Mangoldt sum with $\psi(X)$
-- statement:
--   This is the quantitative core of the comparison between the smoothed Chebyshev sum and $\psi$, stated with all constants explicit and with the needed properties of the smoothing abstracted as hypotheses. Let $\mathrm{Smooth1}$ be any operation producing, from a kernel $F$ and a parameter $\epsilon$, a function $x \mapsto \widetilde{1_\epsilon}(x)$, and assume: constants $0 < c_1 < 1$ and $0 < c_2 < 2$ are given; $\widetilde{1_\epsilon}(x) = 0$ whenever $\epsilon \in (0,1)$ and $x \ge 1 + c_2 \epsilon$; and, along the sample points $x = n / X$ ($n \ge 1$), the values $\widetilde{1_\epsilon}(n/X)$ lie in $[0, 1]$, equal $1$ when $n \le X(1 - c_1 \epsilon)$, and equal $0$ when $n / X \ge 1 + c_2 \epsilon$. Fix $\epsilon \in (0, 1)$ and $X > 3$ satisfying the mild size conditions $X \epsilon c_1 \ge 1$ and $X \epsilon c_2 \ge 1$, and set $C = 6\,(3 c_1 + c_2)$.
--
--   Then the smoothed von Mangoldt sum is close to the Chebyshev function $\psi(X) = \sum_{n \le X}\Lambda(n)$:
--
--   $$\left\| \sum_{n = 1}^{\infty} \Lambda(n)\, \widetilde{1_\epsilon}\!\left(\frac{n}{X}\right) \;-\; \psi(X) \right\| \;\le\; C\, \epsilon\, X \log X.$$
--
--   The role of this lemma is to isolate the purely arithmetic part of the unsmoothing estimate: given only the plateau, vanishing, and $[0,1]$-boundedness of the smoothed cutoff at rational sample points, the discrepancy is supported on the $O(\epsilon X)$ integers in the transition window, each contributing at most $\Lambda(n) \le \log(\text{window top}) = O(\log X)$. The analytic facts about the actual Mellin-convolution smoothing are supplied separately, keeping this counting argument reusable for any cutoff with the same window profile.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L288-L589

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

theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
      ψ X‖ ≤
    C * ε * X * Real.log X := by sorry
