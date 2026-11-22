-- Prove2me | Theorems.Thm_ShiOptRates_Spider_spider_queries_classical
-- name    : ShiOptRates.Spider.spider_queries_classical
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:27:33.543527+00:00
-- url     : https://prove2.me/theorems/e84194f8-3827-45bd-aa76-6fd81c6d4b33
-- title:
--   Classical SPIDER query bill: $25\,728\,000\,\ell\Delta\sigma/\varepsilon^{3}$
-- statement:
--   This theorem evaluates, in closed form and with fully explicit constants, the total oracle-query bill of the SPIDER variance-reduced schedule under a *classical* mean-estimation cost model.
--
--   The setting is a nonconvex objective with mean-squared smoothness constant $\ell$, initial optimality gap $\Delta$, and stochastic-gradient variance scale $\sigma$; the target accuracy is $\varepsilon>0$. The schedule is Algorithm 7 of Sidford–Zhang, whose parameters are
--
--   1. epoch length $q = 20\sigma/\varepsilon$;
--   2. variance target at an epoch start $\hat\sigma_1 = \varepsilon/40$;
--   3. variance target for an in-epoch increment $\hat\sigma_2 = \frac{\varepsilon}{40}\sqrt{\dfrac{\varepsilon}{10\sigma}}$;
--   4. total iteration budget $\mathcal T = 1600\,\ell\Delta/\varepsilon^{2}$.
--
--   The cost of estimating a quantity of variance scale $s$ to variance target $\hat\sigma$ is modelled by a single two-parameter price function $\mathrm{price}(s,\hat\sigma;p,a) = a\,(s/\hat\sigma)^{p}$, and the total bill is
--
--   $$
--   T(\ell,\Delta,\sigma,\varepsilon;p,a) \;=\; \frac{\mathcal T}{q}\,\mathrm{price}(\sigma,\hat\sigma_1;p,a)\;+\;\mathcal T\,\mathrm{price}(\varepsilon,\hat\sigma_2;p,a),
--   $$
--
--   the first term paying for one fresh estimate at the start of each of the $\mathcal T/q$ epochs and the second for one increment estimate at each of the $\mathcal T$ iterations.
--
--   The classical cost model is the instance $p = 2$, $a = 1$ (plain averaging: reaching variance $\hat\sigma^{2}$ costs $s^{2}/\hat\sigma^{2}$ samples). The claim is that for all real $\ell,\Delta$ and all $\sigma>0$, $\varepsilon>0$,
--
--   $$
--   T(\ell,\Delta,\sigma,\varepsilon;2,1) \;=\; \frac{25\,728\,000\;\ell\,\Delta\,\sigma}{\varepsilon^{3}}.
--   $$
--
--   Both terms scale as $\varepsilon^{-3}$ — the epoch-start term contributes $128\,000\,\ell\Delta\sigma/\varepsilon^{3}$ and the increment term $25\,600\,000\,\ell\Delta\sigma/\varepsilon^{3}$ — so the aggregate is the classical $O(\sigma\ell\Delta\varepsilon^{-3})$ rate of Fang et al., now with the hidden constant exhibited.
--
--   The role of the statement is calibration and unification: the *same* symbolic bill $T$, evaluated at the quantum cost exponents $p=1$, $a=\sqrt d$, returns the Q-SPIDER rate instead. Making the classical constant explicit turns the comparison between cost models into an arithmetic identity rather than an asymptotic remark, and is what allows a crossover threshold between the two models to be stated exactly.
--
--   **Formalization Note** The statement is an identity between real-valued closed-form expressions, so no algorithm, probability space, or convergence claim enters here; the positivity hypotheses on $\sigma$ and $\varepsilon$ are exactly what is needed for the divisions and for the square root in $\hat\sigma_2$ to simplify. The iteration budget is taken with $\varepsilon^{2}$ in the denominator; the published parameter block writes $\sigma^{2}$ there, which is inconsistent with the source's own theorem statement and is recorded in the library as a typo.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Spider.lean#L188-L197 (commit 4c0b84980914...) | Reproduces the eps^-3 classical SPIDER query complexity of Fang et al., as cited by Sidford & Zhang, arXiv:2308.01582. | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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

theorem ShiOptRates.Spider.spider_queries_classical (ℓ Δ σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    spiderTotal ℓ Δ σ ε 2 1 = 25728000 * ℓ * Δ * σ / ε ^ 3 := by sorry
