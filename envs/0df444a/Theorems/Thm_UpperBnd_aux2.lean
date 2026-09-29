-- Prove2me | Theorems.Thm_UpperBnd_aux2
-- name    : UpperBnd_aux2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:04:02.193463+00:00
-- url     : https://prove2.me/theorems/02b1f65e-f981-41f5-b9b3-5c3914fe755c
-- title:
--   Exponential bound $|t|^{1-\sigma} \le e^A$ for $\sigma$ to the right of $1 - A/\log|t|$
-- statement:
--   Let $A, \sigma, t$ be real numbers. Assume that $|t| > 3$, and that $\sigma$ lies to the right of the classical zero-free-region boundary at height $t$, i.e.
--   $$\sigma \ge 1 - \frac{A}{\log |t|}.$$
--   Then the power $|t|^{1-\sigma}$ is bounded by an absolute constant depending only on $A$:
--   $$|t|^{1-\sigma} \le e^{A}.$$
--
--   This elementary estimate is the standard mechanism by which the factor $|t|^{1-\sigma}$, which appears in Euler-Maclaurin expansions of $\zeta(\sigma + it)$, is absorbed into a constant throughout the region $\sigma \ge 1 - A/\log|t|$. It is used repeatedly in the derivation of the upper bounds $|\zeta(\sigma+it)| \ll \log|t|$ and $|\zeta'(\sigma+it)| \ll \log^2|t|$ near the $1$-line.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1269-L1277

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

theorem UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by sorry
