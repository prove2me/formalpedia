-- Prove2me | Theorems.Thm_SmoothedChebyshevClose
-- name    : SmoothedChebyshevClose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:03:34.360717+00:00
-- url     : https://prove2.me/theorems/93af0316-cba6-4169-87d8-0da0c76d01fc
-- title:
--   The smoothed Chebyshev function approximates $\psi$: $\|\psi_\epsilon(X) - \psi(X)\| \le C\,\epsilon\, X \log X$
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$, supported in $[1/2, 2]$, nonnegative on $(0, \infty)$, and of multiplicative mass one $\int_0^\infty F(x)\, dx / x = 1$. Let $\psi_\epsilon(X) = \mathrm{SmoothedChebyshev}\,F\,\epsilon\,X$ denote the smoothed Chebyshev function, the version of $\psi(X) = \sum_{n \le X} \Lambda(n)$ in which the sharp cutoff at $X$ is replaced by the smoothed cutoff $\widetilde{1_\epsilon}(n/X)$ built from $F$.
--
--   Then there is a constant $C > 0$, depending only on the kernel, such that for every $X > 3$ and every $\epsilon$ with $0 < \epsilon < 1$ and $X \epsilon > 2$,
--
--   $$\big\| \psi_\epsilon(X) - \psi(X) \big\| \;\le\; C\, \epsilon\, X \log X.$$
--
--   This is the "unsmoothing" estimate of the smoothed approach to the Prime Number Theorem: since the smoothed and sharp cutoffs differ only on the window $n / X \in [1 - O(\epsilon),\, 1 + O(\epsilon)]$, the discrepancy is at most the von Mangoldt mass of an interval of length $O(\epsilon X)$, which is $O(\epsilon X \log X)$ by a Chebyshev-type bound. Combined with the contour-integral evaluation $\psi_\epsilon(X) = X + \text{error}$, choosing $\epsilon$ appropriately in terms of $X$ yields the Prime Number Theorem with error term for $\psi$ itself.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L591-L688

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

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by sorry
