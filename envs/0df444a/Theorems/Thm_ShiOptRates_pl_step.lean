-- Prove2me | Theorems.Thm_ShiOptRates_pl_step
-- name    : ShiOptRates.pl_step
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:50:47.717987+00:00
-- url     : https://prove2.me/theorems/acfa1e07-a002-4833-89f6-3068b280a102
-- title:
--   One inexact gradient step under Polyak--Łojasiewicz contracts the gap by $1-\mu/L$ plus $\delta^2/(2L)$
-- statement:
--   Let $E$ be a real inner-product space, $f : E \to \mathbb{R}$ an objective, and $g : E \to E$ a map playing the role of its gradient. Assume two conditions with the same pair $(f,g)$:
--
--   1. **Smoothness**, in the quadratic-upper-bound form with constant $L > 0$: $f(y) \le f(x) + \langle g(x), y-x\rangle + \tfrac{L}{2}\lVert y-x\rVert^{2}$ for all $x,y$.
--   2. **Polyak--Łojasiewicz gradient domination** with modulus $\mu > 0$ about the value $f^\star$: $2\mu\,(f(x) - f^\star) \le \lVert g(x)\rVert^{2}$ for all $x$.
--
--   Fix $x \in E$ and let $g_d \in E$ be the oracle's output at $x$, accurate to level $\delta$ in the sense that $\lVert g_d - g(x)\rVert \le \delta$. Then one step of size $1/L$ satisfies
--
--   $$
--   f\!\left(x - L^{-1} g_d\right) - f^\star
--   \;\le\; \left(1 - \frac{\mu}{L}\right)\left(f(x) - f^\star\right) + \frac{\delta^{2}}{2L}.
--   $$
--
--   The parameters are: $L$ the smoothness constant, $\mu$ the PL modulus, $f^\star$ the reference value appearing in the PL condition, and $\delta$ the oracle's accuracy at this step.
--
--   The role of the result is to convert *additive* progress into *multiplicative* progress. Without gradient domination, a descent step reduces the objective by an amount proportional to $\lVert g(x)\rVert^{2}$; the PL condition turns that into a fixed fraction $\mu/L$ of the remaining gap, so iterating gives linear convergence with contraction factor $1-\mu/L$ and an additive noise term $\delta^{2}/(2L)$ per step. Summing the geometric series yields the familiar bound $(1-\mu/L)^{K}(f(x_0)-f^\star) + \delta^{2}/(2\mu)$: the gap contracts geometrically down to an $O(\delta^{2}/\mu)$ floor set by the oracle's accuracy. Instantiating $\delta$ at different oracle contracts and cost models is what turns this single step into the exact, inexact and quantum rates under PL.
--
--   **Formalization Note** The hypotheses are the predicates `QuadUpper f g L` and `PolyakLojasiewicz f g mu fstar`; $g$ is an arbitrary map satisfying them alongside $f$, so no differentiability is assumed. The strict positivity of $\mu$ is stated but not required by the algebra of this single step (it is what makes the factor $1-\mu/L$ a genuine contraction on iteration) and is marked unused in Lean.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/PL.lean#L43-L61 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/PL.lean
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
import Theorems.Thm_ShiOptRates_descent_step
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
# Linear convergence under Polyak–Łojasiewicz

Until this file, `PolyakLojasiewicz` and `QuadLower` were *defined* but consumed by no rate
theorem: the library proved exactly one criterion, `min_k ‖∇f(x_k)‖ ≤ ε`.  This adds the
second, and it is the one a classical optimization audience asks for first — linear
convergence of the *function value* — under the same inexact oracle.

The result has the shape every noisy linearly-convergent method has: a geometric term that
decays and a noise floor that does not.

`f(x_K) - f⋆ ≤ (1 - μ/L)^K (f(x_0) - f⋆) + δ²/(2μ)`

Both constants are exact, and the induction establishing it is an equality at the inductive
step — `δ²/(2L) = (δ²/(2μ))(1 - ρ)` — so nothing is lost.

Note where `μ` sits: the noise floor is `δ²/(2μ)`, not `δ²/(2L)`. Ill-conditioning hurts
the floor, not just the rate; requesting accuracy `δ = √(μ ε)` is what buys `ε` of function
value, so the *cost* of a PL rate scales with the condition number through the oracle, not
only through the iteration count.

## Main results

* `pl_step` — one step: `a_{k+1} ≤ (1 - μ/L) a_k + δ_k²/(2L)` where `a_k = f(x_k) - f⋆`.
* `pl_rate` — the geometric recursion solved, with the noise floor.
* `pl_gap_le` — the `ε`-form: `δ ≤ √(μ ε)` and `ρ^K a_0 ≤ ε/2` give `f(x_K) - f⋆ ≤ ε`.
-/

section
open ShiOptRates

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L mu fstar : ℝ}

theorem ShiOptRates.pl_step (hL : 0 < L) (_hmu : 0 < mu) (hQ : QuadUpper f g L)
    (hPL : PolyakLojasiewicz f g mu fstar) (x gd : E) {δ : ℝ}
    (herr : ‖gd - g x‖ ≤ δ) :
    f (x - L⁻¹ • gd) - fstar ≤ (1 - mu / L) * (f x - fstar) + δ ^ 2 / (2 * L) := by sorry
