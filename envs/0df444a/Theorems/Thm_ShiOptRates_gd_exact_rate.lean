-- Prove2me | Theorems.Thm_ShiOptRates_gd_exact_rate
-- name    : ShiOptRates.gd_exact_rate
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T23:05:04.527176+00:00
-- url     : https://prove2.me/theorems/4dfc7237-837f-421e-86d4-4d7f7bf743f2
-- title:
--   Exact gradient descent, smooth nonconvex: $K \ge 2L\Delta_0/\varepsilon^{2}$ gives $\|\nabla f(x_k)\|\le\varepsilon$
-- statement:
--   This is the textbook $\varepsilon^{-2}$ complexity bound for gradient descent on a smooth nonconvex objective, with the constant made explicit and checked.
--
--   Let $E$ be a real inner-product space, $f : E \to \mathbb R$, and $g : E \to E$ its gradient field. Assume $f$ satisfies the quadratic upper bound with constant $L>0$,
--   $$f(y) \le f(x) + \langle g(x),\, y-x\rangle + \tfrac{L}{2}\|y-x\|^{2}\qquad\text{for all }x,y,$$
--   which is the descent-lemma form of $L$-smoothness. Fix a target accuracy $\varepsilon>0$, a horizon $K>0$, and a reference value $f^\star$ with $f^\star \le f(x_K)$. Let $(x_k)$ be the exact gradient-descent trajectory at stepsize $1/L$,
--   $$x_{k+1} = x_k - L^{-1} g(x_k)\qquad (k<K),$$
--   and write $\Delta_0 = f(x_0) - f^\star$ for the initial optimality gap. If the horizon satisfies $2L\Delta_0/\varepsilon^{2} \le K$, then
--
--   $$
--   \exists\, k < K \quad\text{such that}\quad \|g(x_k)\| \;\le\; \varepsilon .
--   $$
--
--   The theorem is the calibration point of the library: it is the $\delta = 0$, deterministic member of a family in which the gradient oracle is a parameter. The same rate mechanism, instantiated at an inexact oracle, gives $K \ge 4L\Delta_0/\varepsilon^{2}$; instantiated at a stochastic oracle, it gives the $\varepsilon^{-4}$ SGD bound. Recovering the classical constant $2L\Delta_0/\varepsilon^{2}$ exactly is what certifies that the parametrized machinery has not silently degraded the known bound.
--
--   **Formalization Note** Only the descent-lemma inequality is assumed; no differentiability, convexity, or global lower bound on $f$ is required beyond the single inequality $f^\star \le f(x_K)$ at the final iterate, which is what makes $\Delta_0$ meaningful. The conclusion is an existence claim over indices strictly below $K$, not a bound on the last iterate.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Calibration.lean#L40-L62 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Calibration.lean
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
import Theorems.Thm_ShiOptRates_exists_grad_sq_le
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# §5 — Calibration theorems

The library's evidence: named rates, stated with explicit constants, each obtained by
instantiating the *same* L1/L2 theorems at a different oracle contract and cost model.

| theorem | layer | rate |
|---|---|---|
| `gd_exact_rate` | L1 | `K ≥ 2LΔ₀/ε²` gradient evaluations |
| `inexact_gd_rate` | L1 | `K ≥ 4LΔ₀/ε²` iterations at accuracy `ε/√2` |
| `minibatch_query_count` | L1 | `≍ 8 L Δ₀ σ² / ε⁴` samples |
| `quantum_query_count` | L1+L2 | `≍ 4√2 · L Δ₀ σ √dim log(K/η) / ε³` queries |

The classical `ε⁻⁴` and the quantum `ε⁻³` are produced by the same iteration bound
`K ≍ 4LΔ₀/ε²` multiplied by two different unit prices; nothing else differs.  See
`Optrates.Cost` for why those two prices are one formula at two exponents.

**Not formalized here** (L3+, per the plan's layering): SGD's `ε⁻⁴` *under an unbiased
stochastic oracle over an adaptive filtration*, SPIDER's `ε⁻³`, and Q-SPIDER's `ε⁻⁵ᐟ²`.
The `ε⁻⁴` below is the deterministic-surrogate version — a minibatch large enough to give
a *deterministic* accuracy guarantee — which is a strictly stronger oracle assumption than
SGD's and therefore not a reproduction of Ghadimi–Lan.  Stating this distinction rather
than eliding it is the point of the layering.
-/

section
open ShiOptRates

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L : ℝ}

theorem ShiOptRates.gd_exact_rate (hL : 0 < L) (hQ : QuadUpper f g L) {fstar ε : ℝ} (hε : 0 < ε)
    (x : ℕ → E) (K : ℕ) (hK : 0 < K) (hlow : fstar ≤ f (x K))
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • g (x k))
    (hKbig : 2 * L * (f (x 0) - fstar) / ε ^ 2 ≤ (K : ℝ)) :
    ∃ k < K, ‖g (x k)‖ ≤ ε := by sorry
