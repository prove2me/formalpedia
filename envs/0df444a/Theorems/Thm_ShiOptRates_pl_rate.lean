-- Prove2me | Theorems.Thm_ShiOptRates_pl_rate
-- name    : ShiOptRates.pl_rate
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:59:16.731581+00:00
-- url     : https://prove2.me/theorems/4c7abb30-4fa9-4d0e-a7ec-71192baf8cf6
-- title:
--   Linear convergence under Polyak–Łojasiewicz with an inexact gradient, and its $\delta^{2}/(2\mu)$ noise floor
-- statement:
--   This theorem gives the linear-convergence rate of inexact gradient descent on a smooth objective satisfying the Polyak–Łojasiewicz (PL) condition, together with the exact size of the accuracy floor imposed by the oracle error.
--
--   Let $E$ be a real inner-product space, $f : E \to \mathbb R$ with gradient field $g : E \to E$, and let $f^\star$ be a reference value. Assume:
--
--   1. **Smoothness.** $f(y) \le f(x) + \langle g(x), y-x\rangle + \tfrac{L}{2}\|y-x\|^{2}$ for all $x,y$, with $L>0$.
--   2. **PL condition** with modulus $\mu$: $\;2\mu\,(f(x)-f^\star) \le \|g(x)\|^{2}$ for all $x$, with $0<\mu\le L$.
--   3. **Update rule.** $x_{k+1} = x_k - L^{-1}\hat g_k$ for $k<K$, where $\hat g_k$ is the oracle's answer at $x_k$.
--   4. **Oracle contract.** $\|\hat g_k - g(x_k)\| \le \delta$ for $k<K$, with $\delta \ge 0$.
--
--   Writing $\rho = 1-\mu/L \in [0,1)$ for the contraction factor, the conclusion is
--
--   $$
--   f(x_K) - f^\star \;\le\; \rho^{K}\,\big(f(x_0)-f^\star\big) \;+\; \frac{\delta^{2}}{2\mu}\,\big(1-\rho^{K}\big).
--   $$
--
--   The bound separates two effects cleanly. The first term is geometric decay at rate $\rho$ per iteration — the classical PL linear rate, recovered exactly at $\delta = 0$. The second term is a *noise floor*: as $K \to \infty$ the guarantee saturates at $\delta^{2}/(2\mu)$, so an oracle of fixed accuracy $\delta$ buys accuracy in objective value proportional to $\delta^{2}$, not $\delta$. The floor constant is not slack: the inductive requirement is $\delta^{2}/(2L) \le \frac{\delta^{2}}{2\mu}(1-\rho)$, and $1-\rho = \mu/L$ makes this an equality.
--
--   Within the library this is the strongly-convex-like regime of the oracle-parametrized rate family: the same $\delta$-schedule interface that yields $\varepsilon^{-2}$ complexity in the nonconvex case yields linear convergence plus an explicit floor here, and the floor is what a downstream cost model must budget against when choosing $\delta$.
--
--   **Formalization Note** Both the smoothness and PL hypotheses are stated as bare inequalities over all points, so no differentiability of $f$ is assumed; $g$ is simply a given vector field playing the role of the gradient. The hypothesis $\mu \le L$ is what keeps $\rho \ge 0$, and $\delta \ge 0$ is carried but not otherwise used in the statement's shape.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/PL.lean#L63-L98 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_pl_step
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

theorem ShiOptRates.pl_rate (hL : 0 < L) (hmu : 0 < mu) (hmuL : mu ≤ L) (hQ : QuadUpper f g L)
    (hPL : PolyakLojasiewicz f g mu fstar) {δ : ℝ} (_hδ : 0 ≤ δ)
    (x gd : ℕ → E) (K : ℕ)
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ δ) :
    f (x K) - fstar
      ≤ (1 - mu / L) ^ K * (f (x 0) - fstar) + δ ^ 2 / (2 * mu) * (1 - (1 - mu / L) ^ K) := by sorry
