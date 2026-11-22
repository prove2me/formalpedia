-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_variance_purchase_classical
-- name    : ShiOptRates.Stochastic.variance_purchase_classical
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:30:32.976221+00:00
-- url     : https://prove2.me/theorems/9cf9c225-e5db-4511-8fba-5f3b550abf9b
-- title:
--   Classical variance reduction is cost-neutral: the total bill is $8aL\Delta/\varepsilon^{4}$, independent of the oracle variance
-- statement:
--   Consider stochastic gradient descent on an $L$-smooth objective with initial objective gap $\Delta$, run to target accuracy $\varepsilon$ with a gradient oracle whose noise variance is $\hat{\sigma}^{2}$. The iteration count supplied by the underlying SGD rate is
--
--   $$
--   N(\hat{\sigma}) \;=\; \frac{8\,L\,\Delta\,\hat{\sigma}^{2}}{\varepsilon^{4}},
--   $$
--
--   and the price of one query at variance $\hat{\sigma}^{2}$ is taken from the power-law cost family $\hat{\sigma} \mapsto a/\hat{\sigma}^{p}$, where $a \ge 0$ is a prefactor and $p \in \mathbb{N}$ is the cost exponent. The *total* query bill is the product,
--
--   $$
--   \mathrm{variancePurchaseTotal}(a, L, \Delta, \varepsilon, \hat{\sigma}; p)
--   \;=\; N(\hat{\sigma}) \cdot \frac{a}{\hat{\sigma}^{p}} .
--   $$
--
--   The theorem evaluates this at the classical exponent $p = 2$, which is the cost of ordinary sample averaging. For $a \ge 0$ and $\hat{\sigma} \neq 0$,
--
--   $$
--   \mathrm{variancePurchaseTotal}(a, L, \Delta, \varepsilon, \hat{\sigma}; 2)
--   \;=\; \frac{8\,a\,L\,\Delta}{\varepsilon^{4}} .
--   $$
--
--   The oracle variance $\hat{\sigma}$ has cancelled out entirely. Every factor gained by driving the variance down — fewer iterations — is paid back exactly in the per-query price, so a classical sampler cannot buy its way below the $\varepsilon^{-4}$ complexity by minibatching. The contrast is with the quantum exponent $p = 1$, where the same formula leaves a single factor of $\hat{\sigma}$ in the bill and reducing the variance is strictly profitable; the classical/quantum separation is thereby localized in one natural number.
--
--   **Formalization Note** The cost model is a structure carrying the price function together with nonnegativity at positive accuracies, and the prefactor's nonnegativity hypothesis $0 \le a$ is what makes that structure well formed; only $\hat{\sigma} \neq 0$ is needed for the cancellation.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/VariancePurchase.lean#L64-L70 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/VariancePurchase.lean
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
import Definitions.Def_ShiOptrates_Stochastic_Bridge
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Definitions.Def_ShiOptrates_Stochastic_VariancePurchase
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Martingale.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# The mechanism: buying variance, and why the cost exponent decides everything

`Stochastic.sgd_rate` needs `K ≥ 8 L Δ₀ σ̂² / ε⁴` iterations from an oracle whose variance
is `σ̂²`.  But `σ̂` is not given by nature — it is *purchased*.  An oracle that averages
samples, or a quantum mean estimator, delivers variance `σ̂²` at a price
`price(σ̂) = a / σ̂ ^ p`, and `p` is the whole story:

| `p` | estimator | total queries |
|---|---|---|
| `2` | classical averaging, `a = L²` | `8 a L Δ₀ / ε⁴` — **independent of `σ̂`** |
| `1` | quantum mean estimation, `a ≍ L√d` | `8 a L Δ₀ σ̂ / ε⁴` — **strictly decreasing in `σ̂`** |

At `p = 2` the `σ̂²` in the iteration count cancels the `σ̂⁻²` in the price exactly, so
buying variance reduction is *cost-neutral*: this is the formal reason a classical sampler
cannot improve SGD's `ε⁻⁴` by averaging harder.  At `p = 1` the cancellation is incomplete
and the purchase is strictly profitable.  That broken tie is the mechanism behind every
quantum stochastic-optimization speedup in the literature.

This is the library's central abstraction discharged at L3: the classical and quantum
analyses share the oracle contract (*unbiased, variance `σ̂²`*) and the entire rate
analysis, and differ in one natural number.

Note which contract appears here: **unbiased**, not bounded-error.  Sidford–Zhang
(arXiv:2308.01582) make exactly this choice, debiasing the quantum estimator by MLMC
before using it, because — in their words — its bias "hinders its combination with various
optimization algorithms assuming unbiased inputs".  `Stochastic.accumulation_linear_tight`
is the machine-checked form of that obstruction.

## Main results

* `variance_purchase_total` — the total query bill as a function of `σ̂` and `p`.
* `variance_purchase_classical` — at `p = 2` the bill does not depend on `σ̂`.
* `variance_purchase_quantum` — at `p = 1` it is linear in `σ̂`.
* `variance_purchase_strict_gain` — hence strictly profitable to reduce `σ̂` when `p = 1`
  and exactly neutral when `p = 2`.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open CostModel

theorem ShiOptRates.Stochastic.variance_purchase_classical (a L Δ ε σhat : ℝ) (ha : 0 ≤ a) (hσ : σhat ≠ 0) :
    variancePurchaseTotal a L Δ ε σhat 2 ha = 8 * a * L * Δ / ε ^ 4 := by sorry
