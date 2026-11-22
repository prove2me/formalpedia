-- Prove2me | Theorems.Thm_ShiOptRates_descent_step
-- name    : ShiOptRates.descent_step
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:31:15.766798+00:00
-- url     : https://prove2.me/theorems/8b7b137e-eb9f-4f71-81a4-ba431d65f827
-- title:
--   One gradient-descent step under an inexact oracle: $\|g(x)\|^2 \le 2L(f(x)-f(x-L^{-1}g_d)) + \|g_d-g(x)\|^2$
-- statement:
--   Let $E$ be a real inner-product space, $f : E \to \mathbb{R}$ an objective and $g : E \to E$ a map satisfying the quadratic upper bound with constant $L > 0$,
--
--   $$
--   f(y) \;\le\; f(x) + \langle g(x),\, y - x\rangle + \tfrac{L}{2}\lVert y - x\rVert^{2}
--   \qquad \text{for all } x, y \in E .
--   $$
--
--   Fix a point $x \in E$ and let $g_d \in E$ be whatever the gradient oracle actually returns at $x$ — an arbitrary vector, not assumed close to $g(x)$. Taking the standard step of size $1/L$ in the direction $-g_d$ gives
--
--   $$
--   \lVert g(x)\rVert^{2} \;\le\; 2L\left(f(x) - f\!\left(x - L^{-1} g_d\right)\right) + \lVert g_d - g(x)\rVert^{2}.
--   $$
--
--   In words: the squared true gradient norm at $x$ is controlled by the objective decrease actually achieved, plus the squared oracle error.
--
--   Two features are worth noting. First, the oracle output $g_d$ is a *parameter*, not an assumption: the inequality holds for every $g_d$, and specializing it ($g_d = g(x)$, a bounded-error classical estimate, a quantum mean estimate) is what yields the exact, inexact and quantum rates from a single lemma. Second, the error term appears with constant exactly $1$: writing $e = g_d - g(x)$, the linear and quadratic terms of the descent lemma combine into $\lVert g(x)\rVert^{2} - \lVert e\rVert^{2}$ identically, so nothing is conceded to an inequality on the cross term. Telescoping this one-step bound over $K$ iterations, with an initial gap $\Delta_0$ and an error schedule, is what produces the explicit horizons elsewhere in the library.
--
--   **Formalization Note** The smoothness hypothesis is the predicate `QuadUpper f g L`; since $g$ is an arbitrary map satisfying that inequality with $f$, no differentiability of $f$ is assumed anywhere. The statement is purely deterministic and mentions no probability.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Deterministic.lean#L42-L78 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Deterministic.lean
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
# L1 — Deterministic core

Inexact gradient descent on an `L`-smooth, lower-bounded objective, driven by an oracle
whose error is *deterministically* bounded by a per-iteration accuracy `δ k`.  There is no
probability anywhere in this file: no filtration, no conditional expectation, no
martingale.  That is the point — a quantum mean estimator's guarantee, conditioned on not
failing, is deterministic, so the quantum rate needs only this layer plus a union bound
(`Optrates.Failure`).

All constants are explicit.

## Main results

* `descent_step` — one step at stepsize `1/L`:
  `‖g x‖² ≤ 2L (f x - f x⁺) + ‖gᵈ - g x‖²`.
  The oracle error enters *additively and squared*, with constant `1`; the cross terms
  cancel exactly, so no Cauchy–Schwarz and no Young inequality is needed here.
* `telescope` — `∑_{k<K} ‖g xₖ‖² ≤ 2L (f x₀ - f x_K) + ∑_{k<K} δₖ²`.
* `exists_grad_sq_le` — the same bound divided by `K`, at some iterate.
* `exists_grad_le_of_const_schedule` — the ε-form: `δₖ² ≤ ε²/2` and `K ≥ 4LΔ₀/ε²` give an
  iterate with `‖g xₖ‖ ≤ ε`.
* `queries_of_const_schedule`, `queries_powerCost` — the query bill for that run,
  in closed form, as a function of the cost exponent.
-/

section
open ShiOptRates

open scoped InnerProductSpace
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L : ℝ}

theorem ShiOptRates.descent_step (hL : 0 < L) (hQ : QuadUpper f g L) (x gd : E) :
    ‖g x‖ ^ 2 ≤ 2 * L * (f x - f (x - L⁻¹ • gd)) + ‖gd - g x‖ ^ 2 := by sorry
