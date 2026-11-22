-- Prove2me | Theorems.Thm_ShiOptRates_inexact_gd_rate
-- name    : ShiOptRates.inexact_gd_rate
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T23:08:50.541879+00:00
-- url     : https://prove2.me/theorems/10c21310-8ec3-423a-8775-39484781f4ca
-- title:
--   Inexact gradient descent: $K \ge 4L\Delta_0/\varepsilon^{2}$ iterations at oracle accuracy $\varepsilon/\sqrt{2}$ give an $\varepsilon$-critical iterate
-- statement:
--   Let $E$ be a real inner-product space and let $f : E \to \mathbb{R}$ with $g : E \to E$ in the role of its gradient satisfy the quadratic upper bound with constant $L > 0$,
--
--   $$
--   f(y) \;\le\; f(x) + \langle g(x),\, y - x\rangle + \frac{L}{2}\lVert y - x\rVert^{2}
--   \qquad \text{for all } x, y \in E .
--   $$
--
--   Fix a target accuracy $\varepsilon > 0$, an iteration count $K > 0$, iterates $(x_k)_{k \in \mathbb{N}}$ in $E$, and inexact gradients $(\hat{g}_k)_{k \in \mathbb{N}}$ in $E$. Let $f^{\star} \in \mathbb{R}$ satisfy $f^{\star} \le f(x_K)$ and put $\Delta_0 = f(x_0) - f^{\star}$. Assume:
--
--   1. **Gradient-descent step at the smoothness stepsize.** $x_{k+1} = x_k - L^{-1}\hat{g}_k$ for all $k < K$.
--   2. **Constant accuracy schedule.** $\lVert \hat{g}_k - g(x_k)\rVert \le \varepsilon/\sqrt{2}$ for all $k < K$.
--   3. **Iteration budget.** $\displaystyle \frac{4\,L\,\Delta_0}{\varepsilon^{2}} \le K$.
--
--   Then some iterate along the run is $\varepsilon$-critical:
--
--   $$
--   \exists\, k < K, \qquad \lVert g(x_k)\rVert \;\le\; \varepsilon .
--   $$
--
--   This is the library's central deterministic rate: the oracle is a parameter, not an assumption. Nothing probabilistic appears — the oracle is described purely by the per-step accuracy request $\varepsilon/\sqrt{2}$ — and the classical, inexact-gradient, and quantum complexity statements are all obtained by pairing this single theorem with different cost models for meeting that accuracy request. The constant $4L\Delta_0/\varepsilon^{2}$ is exactly twice the exact-gradient constant $2L\Delta_0/\varepsilon^{2}$: the factor two is the explicit price of the $\varepsilon/\sqrt{2}$ error budget.
--
--   **Formalization Note** As elsewhere in the library, the gradient is a separate function $g$ constrained only by the quadratic upper bound, and $f^{\star}$ need only lower-bound the objective at the terminal iterate $x_K$, not globally.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Calibration.lean#L69-L79 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_exists_grad_le_of_const_schedule
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

theorem ShiOptRates.inexact_gd_rate (hL : 0 < L) (hQ : QuadUpper f g L) {fstar ε : ℝ} (hε : 0 < ε)
    (x : ℕ → E) (gd : ℕ → E) (K : ℕ) (hK : 0 < K) (hlow : fstar ≤ f (x K))
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ ε / Real.sqrt 2)
    (hKbig : 4 * L * (f (x 0) - fstar) / ε ^ 2 ≤ (K : ℝ)) :
    ∃ k < K, ‖g (x k)‖ ≤ ε := by sorry
