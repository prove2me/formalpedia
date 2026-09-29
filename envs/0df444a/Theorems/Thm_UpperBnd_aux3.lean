-- Prove2me | Theorems.Thm_UpperBnd_aux3
-- name    : UpperBnd_aux3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:50:18.433803+00:00
-- url     : https://prove2.me/theorems/33d02095-f8eb-4fd9-887d-886d6c99dc22
-- title:
--   Truncated Dirichlet sum bound: $\bigl\|\sum_{n \le \lfloor|t|\rfloor} n^{-(\sigma+it)}\bigr\| \le e^A C \log|t|$ near the $1$-line
-- statement:
--   Let $A, C, \sigma, t$ be real numbers with $A \in (0, \tfrac12]$, $C \ge 2$, and $|t| > 3$. Assume $\sigma$ lies in the region
--   $$\sigma \ge 1 - \frac{A}{\log |t|}.$$
--   Set $N = \lfloor |t| \rfloor$ (the natural-number floor of $|t|$). Then the initial segment of the Dirichlet series for $\zeta$, truncated at height $N$, satisfies
--   $$\Bigl\| \sum_{n=0}^{N} n^{-(\sigma + it)} \Bigr\| \le e^{A} \, C \, \log |t|,$$
--   where the $n = 0$ term is interpreted as $0$ (as $0^{-s} = 0$ for $s \ne 0$ in the formalization).
--
--   This is the main-sum estimate in the classical proof that $\zeta(\sigma + it) = O(\log |t|)$ in the region $\sigma \ge 1 - A/\log|t|$: each term is bounded by $e^A/n$ (since $n \le |t|$ forces $n^{1-\sigma} \le e^A$), and the harmonic sum up to $|t|$ contributes the factor $\log|t|$. It feeds directly into the Euler-Maclaurin upper bound for $\zeta$ and, after differentiation, for $\zeta'$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1293-L1320

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

theorem UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by sorry
