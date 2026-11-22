-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_exists_le_sq_of_stepsize
-- name    : ShiOptRates.Stochastic.exists_le_sq_of_stepsize
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:58:47.325151+00:00
-- url     : https://prove2.me/theorems/8caf8e10-d3b9-462b-8b77-ada7806c5c84
-- title:
--   The $\varepsilon^{-4}$ horizon for SGD: $K \ge 8L\Delta_0\sigma^2/\varepsilon^4$ forces some $b_k \le \varepsilon^2$
-- statement:
--   This is the arithmetic core of the stochastic-gradient-descent rate, stated as a property of two real sequences so that it is independent of how the recursion was obtained.
--
--   Let $a, b : \mathbb{N} \to \mathbb{R}$ be sequences — think of $a_k = \mathbb{E}\,f(x_k)$ and $b_k = \mathbb{E}\,\lVert \nabla f(x_k)\rVert^{2}$ along SGD. Let $L > 0$ be the smoothness constant, $\sigma > 0$ the gradient-noise scale, $\varepsilon > 0$ the target accuracy, and $K > 0$ the horizon. Say the pair satisfies the *expected-descent recursion* at stepsize $h$ if
--
--   $$
--   a_{k+1} \;\le\; a_k - \frac{h}{2}\,b_k + \frac{L h^{2}\sigma^{2}}{2}
--   \qquad \text{for all } k < K .
--   $$
--
--   Assume this holds at the stepsize
--
--   $$
--   h \;=\; \frac{\varepsilon^{2}}{2L\sigma^{2}},
--   $$
--
--   that $a_K$ is bounded below by some $a^\star$, and that the horizon satisfies
--
--   $$
--   K \;\ge\; \frac{8\,L\,(a_0 - a^\star)\,\sigma^{2}}{\varepsilon^{4}} .
--   $$
--
--   Then there exists an index $k < K$ with
--
--   $$
--   b_k \;\le\; \varepsilon^{2}.
--   $$
--
--   With $\Delta_0 = a_0 - a^\star$ the initial gap, the horizon is the familiar $8L\Delta_0\sigma^{2}/\varepsilon^{4}$, and the conclusion says some iterate before time $K$ is $\varepsilon$-stationary in the mean-square sense.
--
--   The chosen stepsize is exactly the one that sets the recursion's non-decaying noise floor $Lh\sigma^{2}$ to $\varepsilon^{2}/2$, leaving the other half of the budget for the optimization term $2\Delta_0/(hK)$, which is what the horizon hypothesis controls. The tension between a term that decays in $K$ and a floor that does not is what forces $h$ to shrink with $\varepsilon$ and produces the two extra powers of $1/\varepsilon$ relative to the deterministic rate. Note also the regime implicitly selected by these hypotheses: the admissibility condition $h \le 1/L$ amounts to $\varepsilon^{2} \le 2\sigma^{2}$, i.e. the noise-dominated small-$\varepsilon$ regime, which is the only place the $\varepsilon^{-4}$ rate is the right answer.
--
--   **Formalization Note** The recursion is the predicate `ExpectedDescent a b h L σ K`. Following the library's convention, the stepsize is *supplied and verified* rather than derived: it appears as the explicit value $\varepsilon^{2}/(2L\sigma^{2})$ inside the hypothesis rather than as the output of an optimization.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Recursion.lean#L101-L136 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Recursion.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; the proof is replaced by `sorry`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Theorems.Thm_ShiOptRates_Stochastic_exists_le_of_expectedDescent
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3a — The expected-descent recursion

The part of the classical SGD analysis that is *not* probabilistic.  Every
expectation-based rate proof for a first-order method passes through a scalar recursion of
the form

`aₖ₊₁ ≤ aₖ - (h/2) bₖ + L h² σ² / 2`

where `aₖ = E f(xₖ)` and `bₖ = E‖∇f(xₖ)‖²`.  Establishing that recursion is the
probabilistic step (`Optrates.Stochastic.OneStep`); turning it into a rate is real
analysis, and is done here once.

Separating the two is what makes the `ε⁻⁴` bound auditable: the constant `8 L Δ₀ σ² / ε⁴`
below is a consequence of arithmetic on the recursion alone, and no martingale theory can
change it.

## Main results

* `sum_le_of_expectedDescent` — telescoping the recursion.
* `exists_le_of_expectedDescent` — `min_{k<K} bₖ ≤ 2Δ₀/(hK) + L h σ²`, the standard
  two-term bound with both terms explicit.
* `exists_le_sq_of_stepsize` — **GL3's arithmetic core**: at `h = ε²/(2Lσ²)` and
  `K ≥ 8 L Δ₀ σ² / ε⁴` some `bₖ ≤ ε²`.  Stepsize supplied and verified, not derived, per
  the library's convention.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open Finset

variable {a b : ℕ → ℝ} {h L σ : ℝ} {K : ℕ}

theorem ShiOptRates.Stochastic.exists_le_sq_of_stepsize {astar ε : ℝ} (hε : 0 < ε) (hL : 0 < L) (hσ : 0 < σ)
    (hK : 0 < K)
    (hrec : ExpectedDescent a b (ε ^ 2 / (2 * L * σ ^ 2)) L σ K)
    (hlow : astar ≤ a K)
    (hKbig : 8 * L * (a 0 - astar) * σ ^ 2 / ε ^ 4 ≤ (K : ℝ)) :
    ∃ k < K, b k ≤ ε ^ 2 := by sorry
