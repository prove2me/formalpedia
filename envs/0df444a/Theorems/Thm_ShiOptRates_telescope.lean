-- Prove2me | Theorems.Thm_ShiOptRates_telescope
-- name    : ShiOptRates.telescope
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:51:20.976438+00:00
-- url     : https://prove2.me/theorems/9b8e0dec-3475-4b40-9d48-e83df4453cb1
-- title:
--   Telescoped inexact-gradient bound: $\sum_{k<K}\|\nabla f(x_k)\|^{2}\le 2L\big(f(x_0)-f(x_K)\big)+\sum_{k<K}\delta_k^{2}$
-- statement:
--   This is the summed form of the inexact descent step: over a finite horizon, the total squared gradient norm along the trajectory is controlled by the objective decrease plus the total squared oracle error.
--
--   Let $E$ be a real inner-product space, $f : E \to \mathbb R$ with gradient field $g : E \to E$ satisfying the quadratic upper bound with constant $L>0$,
--   $$f(y) \le f(x) + \langle g(x), y-x\rangle + \tfrac{L}{2}\|y-x\|^{2}\qquad\text{for all }x,y.$$
--   Let $K$ be a horizon, $(x_k)$ a trajectory, $(\hat g_k)$ the oracle answers and $(\delta_k)$ the accuracy schedule, subject to
--
--   1. **Update rule.** $x_{k+1} = x_k - L^{-1}\hat g_k$ for every $k<K$;
--   2. **Oracle contract.** $\|\hat g_k - g(x_k)\| \le \delta_k$ for every $k<K$.
--
--   Then
--
--   $$
--   \sum_{k=0}^{K-1} \|g(x_k)\|^{2} \;\le\; 2L\big(f(x_0)-f(x_K)\big) \;+\; \sum_{k=0}^{K-1} \delta_k^{2}.
--   $$
--
--   Two features are worth naming. First, the objective enters only through the *realized* decrease $f(x_0)-f(x_K)$; no lower bound on $f$ is needed here, and supplying one ($f^\star \le f(x_K)$) is what converts this into a complexity statement. Second, the accuracy schedule enters only through $\sum_k \delta_k^{2}$ — the aggregate squared error, not the individual $\delta_k$ — so any schedule with the same total error budget yields the same guarantee.
--
--   This is the pivot of the deterministic layer of the library. Averaging the left-hand side over $k<K$ and combining with a lower bound on $f$ produces the exact-gradient rate at $\delta \equiv 0$ and the inexact rate under a $\delta$-schedule; the constants $2L$ and $1$ in front of the two sums are exactly what make those downstream constants come out as $2L\Delta_0/\varepsilon^{2}$ and $4L\Delta_0/\varepsilon^{2}$ respectively.
--
--   **Formalization Note** The sum is over `Finset.range K`, i.e. indices $0,\dots,K-1$. Only the descent-lemma inequality is assumed about $f$ and $g$; there is no differentiability, convexity, or measure-theoretic content, and the schedule $(\delta_k)$ is an arbitrary real sequence constrained only by the oracle contract at indices below $K$.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Deterministic.lean#L147-L171 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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

theorem ShiOptRates.telescope (hL : 0 < L) (hQ : QuadUpper f g L)
    (x : ℕ → E) (gd : ℕ → E) (δ : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ δ k) :
    ∑ k ∈ range K, ‖g (x k)‖ ^ 2
      ≤ 2 * L * (f (x 0) - f (x K)) + ∑ k ∈ range K, (δ k) ^ 2 := by sorry
