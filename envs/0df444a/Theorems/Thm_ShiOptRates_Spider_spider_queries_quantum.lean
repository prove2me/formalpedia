-- Prove2me | Theorems.Thm_ShiOptRates_Spider_spider_queries_quantum
-- name    : ShiOptRates.Spider.spider_queries_quantum
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:27:53.264227+00:00
-- url     : https://prove2.me/theorems/fa898af5-2b31-4064-897c-18ed1a048dfb
-- title:
--   Q-SPIDER query bill in closed form: $3200\,\ell\Delta\sqrt{d}/\varepsilon^{2} + 64000\,\ell\Delta\sqrt{d}\sqrt{10\sigma}/(\varepsilon^{2}\sqrt{\varepsilon})$
-- statement:
--   This theorem evaluates, in closed form, the total number of oracle queries spent by the SPIDER schedule when the mean estimator is the *quantum* one.
--
--   The parameters are: a smoothness constant $\ell$, an initial objective gap $\Delta$, a noise scale $\sigma > 0$, a target accuracy $\varepsilon > 0$, and a dimension parameter $d \ge 0$ entering through $\sqrt{d}$. The schedule's own quantities are the epoch length $q = 20\sigma/\varepsilon$, the epoch-start variance target $\hat{\sigma}_1 = \varepsilon/40$, the increment variance target $\hat{\sigma}_2 = (\varepsilon/40)\sqrt{\varepsilon/(10\sigma)}$, and the iteration budget $\mathcal{T} = 1600\,\ell\Delta/\varepsilon^{2}$.
--
--   Mean estimation is priced by a single power law: reaching variance $\hat{\sigma}^{2}$ on a quantity of variance scale $s^{2}$ costs $a\,(s/\hat{\sigma})^{p}$ queries. The exponent $p$ is the whole classical/quantum distinction: $p = 2$, $a = 1$ is classical averaging, while $p = 1$, $a = \sqrt{d}$ is quantum multivariate mean estimation. The total bill of the schedule, written $\mathrm{spiderTotal}(\ell, \Delta, \sigma, \varepsilon; p, a)$, is the epoch-start term plus the increment term,
--
--   $$
--   \frac{\mathcal{T}}{q}\cdot a\left(\frac{\sigma}{\hat{\sigma}_1}\right)^{p}
--   \;+\;
--   \mathcal{T}\cdot a\left(\frac{\varepsilon}{\hat{\sigma}_2}\right)^{p}.
--   $$
--
--   At the quantum instance $p = 1$, $a = \sqrt{d}$ this equals
--
--   $$
--   \mathrm{spiderTotal}(\ell, \Delta, \sigma, \varepsilon; 1, \sqrt{d})
--   \;=\;
--   \frac{3200\,\ell\,\Delta\,\sqrt{d}}{\varepsilon^{2}}
--   \;+\;
--   \frac{64000\,\ell\,\Delta\,\sqrt{d}\,\sqrt{10\sigma}}{\varepsilon^{2}\sqrt{\varepsilon}} .
--   $$
--
--   The first term scales as $\varepsilon^{-2}$ and the second as $\varepsilon^{-5/2}$, so the increment term dominates and the total is $\Theta\big(\ell\Delta\sqrt{d\sigma}\,\varepsilon^{-5/2}\big)$ — the published Q-SPIDER rate, but with every constant on display. The companion classical instance $p = 2$, $a = 1$ of the *same* formula yields an $\varepsilon^{-3}$ bill, which is the point of the construction: one schedule and one price list, two published rates.
--
--   **Formalization Note** The exponent $5/2$ is written as $\varepsilon^{2}\sqrt{\varepsilon}$ so that only natural-number powers and square roots occur; no real exponentiation is used. The hypothesis $0 \le d$ is not needed for the identity and is carried only for readability.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Spider.lean#L199-L221 (commit 4c0b84980914...) | Reproduces the query complexity of Sidford & Zhang, Quantum speedups for stochastic optimization, arXiv:2308.01582, Theorem 8 (the O~(lD sqrt(d sigma) eps^-5/2) bound). | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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

theorem ShiOptRates.Spider.spider_queries_quantum (ℓ Δ σ ε d : ℝ) (hσ : 0 < σ) (hε : 0 < ε) (_hd : 0 ≤ d) :
    spiderTotal ℓ Δ σ ε 1 (Real.sqrt d)
      = 3200 * ℓ * Δ * Real.sqrt d / ε ^ 2
        + 64000 * ℓ * Δ * Real.sqrt d * Real.sqrt (10 * σ) / (ε ^ 2 * Real.sqrt ε) := by sorry
