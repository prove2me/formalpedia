-- Prove2me | Theorems.Thm_Tendsto_nhdsWithin_punctured_map_add
-- name    : Tendsto_nhdsWithin_punctured_map_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:52:37.80219+00:00
-- url     : https://prove2.me/theorems/3f38a902-6553-4f2f-8130-8e5dc4627ca4
-- title:
--   A strictly monotone isometry followed by translation preserves right-punctured limits
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$ be a strictly monotone (increasing) isometry of the real line — so $f$ preserves distances and order, hence is of the form $f(y) = y + b$ for some constant $b$ — and let $a, x$ be real numbers. Consider approach to $x$ strictly from the right, i.e. the filter $\mathcal{N}_{>x}$ of neighborhoods of $x$ within $(x, \infty)$.
--
--   Then the map $y \mapsto f(y) + a$ carries right-punctured approach to $x$ to right-punctured approach to $f(x) + a$:
--
--   $$y \to x^{+} \quad\Longrightarrow\quad f(y) + a \to \big(f(x) + a\big)^{+},$$
--
--   that is, $y \mapsto f(y) + a$ tends to the filter $\mathcal{N}_{>(f(x) + a)}$ along $\mathcal{N}_{>x}$.
--
--   This generalizes the pure-translation lemma to any order-preserving isometric change of variable followed by a shift. It is a convenience lemma for the zeta-bounds development, where substitutions of this shape occur in one-sided limit computations attached to contour and boundary estimates.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1828-L1852

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

theorem Tendsto_nhdsWithin_punctured_map_add {f : ℝ → ℝ} (a x : ℝ)
    (f_mono : StrictMono f) (f_iso : Isometry f) :
    Tendsto (fun y ↦ f y + a) (𝓝[>] x) (𝓝[>] (f x + a)) := by sorry
