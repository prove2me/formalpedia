-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_exists_le_of_expectedDescent
-- name    : ShiOptRates.Stochastic.exists_le_of_expectedDescent
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:48:09.538674+00:00
-- url     : https://prove2.me/theorems/c487ec62-386c-4235-b47f-6117c5e906cd
-- title:
--   Two-term bound for an expected-descent recursion: $\min_{k<K} b_k \le 2\Delta_0/(hK) + Lh\sigma^{2}$
-- statement:
--   Let $(a_k)_{k\in\mathbb{N}}$ and $(b_k)_{k\in\mathbb{N}}$ be real sequences, let $h > 0$ be a stepsize, $L$ a smoothness constant, $\sigma$ a noise scale, and $K > 0$ a horizon. Say the pair $(a, b)$ satisfies the **expected-descent recursion** with data $(h, L, \sigma, K)$ if
--
--   $$
--   a_{k+1} \;\le\; a_k - \frac{h}{2}\, b_k + \frac{L\,h^{2}\sigma^{2}}{2}
--   \qquad \text{for all } k < K .
--   $$
--
--   This is the inequality that the pair $\big(\mathbb{E} f(x_k),\ \mathbb{E}\lVert \nabla f(x_k)\rVert^{2}\big)$ satisfies along stochastic gradient descent with stepsize $h$ on an $L$-smooth objective whose gradient noise has second moment at most $\sigma^{2}$; here it is taken as a hypothesis on two bare sequences, so the conclusion is independent of how the recursion was obtained.
--
--   Suppose in addition that $a^{\star} \le a_K$, and write $\Delta_0 = a_0 - a^{\star}$. Then
--
--   $$
--   \exists\, k < K, \qquad b_k \;\le\; \frac{2\,\Delta_0}{h\,K} \;+\; L\,h\,\sigma^{2} .
--   $$
--
--   The right-hand side splits into an *optimization term* $2\Delta_0/(hK)$, which decays in the horizon $K$, and a *noise floor* $Lh\sigma^{2}$, which does not decay in $K$ at all and can be reduced only by shrinking the stepsize. The tension between the two is the entire source of the stochastic slowdown: to drive $\min_k b_k$ below $\varepsilon^{2}$ one must take $h$ of order $\varepsilon^{2}/(L\sigma^{2})$, and the resulting horizon is of order $L\Delta_0\sigma^{2}/\varepsilon^{4}$ — the two extra powers of $1/\varepsilon$ over the deterministic case. Both constants here are explicit, so the $\varepsilon^{-4}$ complexity that follows is a consequence of arithmetic on the recursion alone and no martingale argument can improve it.
--
--   **Formalization Note** The recursion is packaged as a predicate on the two sequences rather than derived from a probability space, and $a^{\star}$ need only lower-bound the terminal value $a_K$.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Recursion.lean#L72-L99 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_Stochastic_sum_le_of_expectedDescent
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

theorem ShiOptRates.Stochastic.exists_le_of_expectedDescent {astar : ℝ} (hh : 0 < h) (hK : 0 < K)
    (hrec : ExpectedDescent a b h L σ K) (hlow : astar ≤ a K) :
    ∃ k < K, b k ≤ 2 * (a 0 - astar) / (h * K) + L * h * σ ^ 2 := by sorry
