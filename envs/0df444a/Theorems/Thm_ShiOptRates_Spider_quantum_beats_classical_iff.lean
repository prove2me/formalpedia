-- Prove2me | Theorems.Thm_ShiOptRates_Spider_quantum_beats_classical_iff
-- name    : ShiOptRates.Spider.quantum_beats_classical_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:27:15.619989+00:00
-- url     : https://prove2.me/theorems/5c5953d6-497f-442d-b4d7-0403ad1630cc
-- title:
--   Q-SPIDER beats classical SPIDER iff $d\varepsilon < 16000\,\sigma$
-- statement:
--   We compare the dominant terms of the query bills of two variance-reduced stochastic gradient methods for smooth nonconvex optimization: classical SPIDER and its quantum mean-estimation variant, Q-SPIDER.
--
--   The parameters are: $\ell > 0$, the mean-squared smoothness constant of the stochastic gradients; $\Delta > 0$, the initial objective gap $f(x_0) - f^\star$; $\sigma > 0$, the gradient-noise scale; $\varepsilon > 0$, the target accuracy (the method returns an approximately stationary point at scale $\varepsilon$); and $d \ge 0$, the ambient dimension, which enters the quantum bill through $\sqrt{d}$.
--
--   With all constants written out, the leading (i.e. slowest-decaying in $\varepsilon$) term of each bill is
--
--   $$
--   Q(\ell,\Delta,\sigma,\varepsilon,d) \;=\; \frac{64000\,\ell\,\Delta\,\sqrt{d}\,\sqrt{10\sigma}}{\varepsilon^{2}\sqrt{\varepsilon}},
--   \qquad
--   C(\ell,\Delta,\sigma,\varepsilon) \;=\; \frac{25\,600\,000\,\ell\,\Delta\,\sigma}{\varepsilon^{3}} .
--   $$
--
--   The quantum term scales as $\varepsilon^{-5/2}$ and the classical one as $\varepsilon^{-3}$. The theorem is the exact crossover between them: for $\ell,\Delta,\sigma,\varepsilon > 0$ and $d \ge 0$,
--
--   $$
--   Q(\ell,\Delta,\sigma,\varepsilon,d) \;<\; C(\ell,\Delta,\sigma,\varepsilon)
--   \quad\Longleftrightarrow\quad
--   d\,\varepsilon \;<\; 16000\,\sigma .
--   $$
--
--   Note that the criterion is an equivalence, and that the smoothness constant $\ell$, the initial gap $\Delta$ and the $\varepsilon$-exponent all cancel: whether the quantum bill is smaller depends only on the product $d\varepsilon$ against $\sigma$.
--
--   The role of the result is to make the folklore "dimension versus accuracy" trade-off of quantum stochastic optimization quantitative. Two readings follow directly from the displayed criterion. First, at fixed dimension $d$ the advantage disappears as $\varepsilon \to 0$: the quantum speedup lives in the moderate-accuracy regime, not the asymptotic one. Second, at fixed accuracy the advantage requires the dimension to stay below the threshold $16000\,\sigma/\varepsilon$, which is consistent with the known large-dimension no-speedup lower bounds for quantum stochastic optimization.
--
--   **Formalization Note** The two dominant terms are packaged as the definitions `quantumIncrement` and `classicalIncrement`, extracted from the full bills proved elsewhere in the library. Half-integer powers are written using `Real.sqrt` (e.g. $\varepsilon^{2}\sqrt{\varepsilon}$ rather than $\varepsilon^{5/2}$), so no real exponentiation appears in the statement.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Spider.lean#L231-L275 (commit 4c0b84980914...) | The exact crossover and its interpretation are the library's own finding (o) in its STATUS notes, where the large-d no-speedup comparison is attributed to ref. [82] therein. | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Spider.lean
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
import Definitions.Def_ShiOptrates_Spider
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
# L4 / GL4 — SPIDER and Q-SPIDER

The recursive variance-reduction rate, at both cost exponents.

SPIDER (Fang et al. 2018) refreshes a full gradient estimate every `q` steps and, in
between, updates it by an estimate of the *increment* `∇f(xₜ) - ∇f(xₜ₋₁)`.  Under mean-
squared smoothness the increment is small — its variance is at most `ℓ²‖xₜ - xₜ₋₁‖²` — so
it can be estimated cheaply, and the accumulated error over an epoch is controlled by
`Stochastic.accumulation_sq`.

Q-SPIDER (Sidford–Zhang, arXiv:2308.01582, Algorithm 7) is the *same algorithm with the
same schedule*, with the classical variance-reduction step replaced by their quantum
variance reduction (their Theorem 4), which delivers an **unbiased** estimate of variance
`σ̂²` at price `√d · scale / σ̂` instead of the classical `scale² / σ̂²`.

So the two published rates, `ε⁻³` and `√d ε⁻⁵ᐟ²`, are the *same schedule* priced at two
cost exponents.  That is what `spider_queries_classical` and `spider_queries_quantum`
below establish, in closed form with explicit constants.

## Main definitions

* `MeanSquaredSmooth` — `E‖G x ω - G y ω‖² ≤ ℓ²‖x - y‖²`, the function class SPIDER needs.
* `mePrice scale σhat p a` — `a · (scale/σhat)^p`: mean-estimation price, classical at
  `p = 2, a = 1` and quantum at `p = 1, a = √d`.
* `spiderTotal` — the query bill of Algorithm 7's schedule at a given exponent.

## Main results

* `increment_variance_le` — the increment-variance bound, and `increment_variance_le_sq`
  its specialization at the algorithm's normalized step `ε/ℓ`.
* `epoch_error_le` — the accumulated epoch error, via `accumulation_sq`.
* `schedule_budget` — **the schedule verification**: Algorithm 7's `(q, σ̂₁, σ̂₂)` spend
  exactly `3ε²/1600` of error budget, so the claimed accuracy holds with slack.
* `spider_queries_classical` — `≍ 2.56·10⁷ · ℓ Δ σ / ε³`.
* `spider_queries_quantum` — `≍ 6.4·10⁴ √10 · ℓ Δ √(dσ) / ε⁵ᐟ²`.
* `quantum_beats_classical_iff` — the crossover: the quantum bill is smaller exactly when
  `d ε < 16000 σ`.  The dimension-versus-accuracy tradeoff, with the constant.

## What this file does and does not establish

It reproduces the **query complexity** of both algorithms, with explicit constants, and the
epoch error control that makes the schedule valid.  It does *not* prove that Algorithm 7's
output is an `ε`-critical point: that is Fang et al.'s Theorem 1, which Sidford–Zhang also
import rather than reprove (their Theorem 9).  The formalization therefore mirrors the
structure of the published proof exactly — correctness cited, query count computed — and
the correctness half remains open.  Closing it means formalizing SPIDER's descent argument
under the normalized step and the `‖vₜ‖ ≤ 2ε` early return.
-/

section
open ShiOptRates
open ShiOptRates.Spider

open MeasureTheory Finset
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The function class -/

/-! ### The epoch error, via the accumulation law -/

variable [IsProbabilityMeasure μ] [CompleteSpace E]

end

/-! ### The schedule and the query bill

From here everything is arithmetic on Algorithm 7's stated parameters:

`q = 20σ/ε`, `σ̂₁ = ε/40`, `σ̂₂ = (ε/40)·√(ε/(10σ))`, budget `𝒯 = 1600 ℓΔ/ε²`.
-/

section
open ShiOptRates
open ShiOptRates.Spider

theorem ShiOptRates.Spider.quantum_beats_classical_iff (ℓ Δ σ ε d : ℝ) (hℓ : 0 < ℓ) (hΔ : 0 < Δ)
    (hσ : 0 < σ) (hε : 0 < ε) (hd : 0 ≤ d) :
    quantumIncrement ℓ Δ σ ε d < classicalIncrement ℓ Δ σ ε ↔ d * ε < 16000 * σ := by sorry
