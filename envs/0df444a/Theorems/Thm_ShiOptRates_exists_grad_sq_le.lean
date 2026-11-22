-- Prove2me | Theorems.Thm_ShiOptRates_exists_grad_sq_le
-- name    : ShiOptRates.exists_grad_sq_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:59:00.264044+00:00
-- url     : https://prove2.me/theorems/6a4d1403-63c8-4b95-b67d-403f4f3282c4
-- title:
--   Inexact gradient descent with an arbitrary accuracy schedule: some iterate has $\lVert \nabla f(x_k)\rVert^{2} \le \big(2L\Delta_0 + \sum_{j<K}\delta_j^{2}\big)/K$
-- statement:
--   Let $E$ be a real inner-product space and let $f : E \to \mathbb{R}$, with $g : E \to E$ in the role of its gradient, satisfy the quadratic upper bound with constant $L > 0$,
--
--   $$
--   f(y) \;\le\; f(x) + \langle g(x),\, y - x\rangle + \frac{L}{2}\lVert y - x\rVert^{2}
--   \qquad \text{for all } x, y \in E .
--   $$
--
--   Fix a horizon $K > 0$, iterates $(x_k)$ and inexact gradients $(\hat{g}_k)$ in $E$, and an arbitrary accuracy schedule $\delta : \mathbb{N} \to \mathbb{R}$. Let $f^{\star} \in \mathbb{R}$ satisfy $f^{\star} \le f(x_K)$ and write $\Delta_0 = f(x_0) - f^{\star}$. Assume:
--
--   1. **Gradient-descent step at the smoothness stepsize.** $x_{k+1} = x_k - L^{-1}\hat{g}_k$ for all $k < K$.
--   2. **Accuracy schedule honoured.** $\lVert \hat{g}_k - g(x_k)\rVert \le \delta_k$ for all $k < K$.
--
--   Then
--
--   $$
--   \exists\, k < K, \qquad
--   \lVert g(x_k)\rVert^{2} \;\le\; \frac{2\,L\,\Delta_0 \;+\; \sum_{j=0}^{K-1} \delta_j^{2}}{K} .
--   $$
--
--   This is the averaging step of the inexact gradient-descent analysis in its most reusable form: the schedule $\delta$ is left free, so the bound applies verbatim to an exact oracle ($\delta \equiv 0$, recovering the classical $2L\Delta_0/K$ bound on the smallest squared gradient norm), to a constant-accuracy oracle, and to decaying or adaptive schedules alike. Specializing to $\delta_k \equiv \varepsilon/\sqrt{2}$ and $K \ge 4L\Delta_0/\varepsilon^{2}$ yields an $\varepsilon$-critical iterate, which is the form the classical, inexact, and quantum complexity statements all consume — the oracle enters only through $\delta$ and through the price paid to meet it.
--
--   **Formalization Note** No sign condition is imposed on $\delta$; it is constrained only through hypothesis (2), which already forces $\delta_k \ge 0$ for $k < K$. As throughout the library, $f^{\star}$ need only lower-bound the objective at the terminal iterate $x_K$, which is all the argument uses, and the gradient is carried as a separate function $g$ rather than via a differentiability assumption.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Deterministic.lean#L173-L198 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_telescope
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

theorem ShiOptRates.exists_grad_sq_le (hL : 0 < L) (hQ : QuadUpper f g L) {fstar : ℝ}
    (x : ℕ → E) (gd : ℕ → E) (δ : ℕ → ℝ) (K : ℕ) (hK : 0 < K)
    (hlow : fstar ≤ f (x K))
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ δ k) :
    ∃ k < K, ‖g (x k)‖ ^ 2
      ≤ (2 * L * (f (x 0) - fstar) + ∑ j ∈ range K, (δ j) ^ 2) / K := by sorry
