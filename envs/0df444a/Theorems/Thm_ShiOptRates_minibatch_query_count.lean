-- Prove2me | Theorems.Thm_ShiOptRates_minibatch_query_count
-- name    : ShiOptRates.minibatch_query_count
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:50:32.139987+00:00
-- url     : https://prove2.me/theorems/59ae82b0-8da8-4eb9-86d8-d91c89077bb6
-- title:
--   Classical minibatch bill: $K$ iterations at accuracy $\varepsilon/\sqrt2$ cost $2K\sigma^2/\varepsilon^2$ samples
-- statement:
--   A classical minibatch mean estimator with noise scale $\sigma$ needs $\sigma^{2}/\delta^{2}$ samples to return a gradient estimate of accuracy $\delta > 0$; this is the cost model $\delta \mapsto \sigma^{2}/\delta^{2}$. Given an accuracy *schedule* $\delta : \mathbb{N} \to \mathbb{R}$ and a horizon $K$, the total bill is $\sum_{k<K} \sigma^{2}/\delta(k)^{2}$.
--
--   The theorem evaluates this total for the constant schedule $\delta(k) \equiv \varepsilon/\sqrt{2}$, the accuracy at which the library's inexact-gradient descent rate is stated. For every $\varepsilon > 0$ and every $K \in \mathbb{N}$,
--
--   $$
--   \sum_{k < K} \frac{\sigma^{2}}{(\varepsilon/\sqrt{2})^{2}} \;=\; K \cdot \frac{2\sigma^{2}}{\varepsilon^{2}} .
--   $$
--
--   Here $\sigma$ is the noise scale of the estimator, $\varepsilon$ the target stationarity accuracy, and $K$ the number of outer iterations.
--
--   The role of the result is to turn an iteration count into a sample count with explicit constants. Composed with the inexact-gradient horizon $K \asymp 4L\Delta_0/\varepsilon^{2}$ (for an $L$-smooth objective with initial gap $\Delta_0$), it gives a total of order $8\,L\,\Delta_0\,\sigma^{2}/\varepsilon^{4}$ samples — the familiar classical $\varepsilon^{-4}$, with the constant. It is the baseline against which the quantum mean-estimation bill, which is linear rather than quadratic in $1/\delta$, is compared elsewhere in the library.
--
--   One caveat is worth stating in the theorem's own terms: this counts the cost of *buying a deterministic $\varepsilon/\sqrt{2}$-accurate gradient at every step*, not the cost of stochastic gradient descent. The genuine SGD $\varepsilon^{-4}$ rate is a separate, probabilistic statement.
--
--   **Formalization Note** The estimator is `CostModel.minibatch σ` and the bill is `CostModel.totalCost`, a finite sum over `Finset.range K`. The positivity hypothesis on $\varepsilon$ is not used by the arithmetic and is marked unused in Lean; it is retained because it is what makes the requested accuracy admissible for the cost model.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Calibration.lean#L81-L94 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_CostModel_totalCost_const
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

theorem ShiOptRates.minibatch_query_count (σ ε : ℝ) (_hε : 0 < ε) (K : ℕ) :
    (CostModel.minibatch σ).totalCost (fun _ => ε / Real.sqrt 2) K
      = K * (2 * σ ^ 2 / ε ^ 2) := by sorry
