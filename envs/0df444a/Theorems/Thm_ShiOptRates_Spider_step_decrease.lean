-- Prove2me | Theorems.Thm_ShiOptRates_Spider_step_decrease
-- name    : ShiOptRates.Spider.step_decrease
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:47:41.015767+00:00
-- url     : https://prove2.me/theorems/ec49e11e-0255-4938-80ca-4b02a57df9a4
-- title:
--   One normalized SPIDER step decreases the objective by $\varepsilon^2/(2\ell)$
-- statement:
--   Let $E$ be a real inner-product space, $f : E \to \mathbb{R}$ an objective and $g : E \to E$ a map playing the role of its gradient. Assume $f$ satisfies the quadratic upper bound (descent-lemma inequality) with constant $\ell > 0$,
--
--   $$
--   f(y) \;\le\; f(x) + \langle g(x),\, y - x\rangle + \tfrac{\ell}{2}\lVert y - x\rVert^{2}
--   \qquad \text{for all } x, y \in E .
--   $$
--
--   Fix an accuracy $\varepsilon > 0$, a point $x \in E$, and a gradient estimate $v \in E$ which is $\varepsilon$-accurate at $x$, i.e. $\lVert v - g(x)\rVert \le \varepsilon$, and which is *large* in the sense of SPIDER's return test, $\lVert v \rVert > 2\varepsilon$. Taking the normalized step of length $\varepsilon/\ell$ in the direction $-v/\lVert v\rVert$ gives
--
--   $$
--   f\!\left(x - \frac{\varepsilon}{\ell}\cdot\frac{v}{\lVert v\rVert}\right)
--   \;\le\; f(x) - \frac{\varepsilon^{2}}{2\ell}.
--   $$
--
--   Thus every step the algorithm takes *before* returning buys a fixed amount $\varepsilon^{2}/(2\ell)$ of objective decrease, independently of the iterate.
--
--   This is the deterministic engine of SPIDER's correctness argument, and the place where the factor of two in the return threshold $\lVert v\rVert \le 2\varepsilon$ earns its keep: the gap between $\lVert v \rVert > 2\varepsilon$ and the estimate's error $\varepsilon$ is what forces the true gradient to have directional derivative at least $\varepsilon$ along the normalized direction. Combined with a lower bound $f \ge f^\star$ and an initial gap $\Delta_0$, the fixed per-step decrease immediately caps the number of non-returning steps by $2\ell\Delta_0/\varepsilon^{2}$.
--
--   **Formalization Note** The smoothness hypothesis is the predicate `QuadUpper f g ℓ`; note that $g$ is an arbitrary map satisfying that inequality with $f$, so no differentiability of $f$ is assumed. The statement is entirely deterministic: it is the conclusion one draws pathwise on the event that the stochastic estimate is $\varepsilon$-accurate.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Spider.lean#L319-L343 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_Spider_inner_dir_ge
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

/-! ### The correctness half: the algorithm cannot run forever without returning

Algorithm 7 takes a *normalized* step of length `ε/ℓ` in the direction `-vₜ/‖vₜ‖`, and
returns `xₜ` as soon as `‖vₜ‖ ≤ 2ε`.  The content of correctness is that it must return
soon: while `‖vₜ‖ > 2ε` and the estimate is `ε`-accurate, every step buys `ε²/(2ℓ)` of
objective decrease, so at most `2ℓΔ₀/ε²` such steps can occur.

Everything here is deterministic, conditioned on the accuracy event `‖vₜ - ∇f(xₜ)‖ ≤ ε`;
`epoch_error_le` is what makes that event likely.  The remaining gap to Fang et al.'s
Theorem 1 is the probabilistic wrapper — bounding `E‖e_τ‖` at the *random* return time `τ`,
where conditioning on `τ = k` breaks the unconditional variance bound.  That step, and only
that step, is still open. -/

section Correctness

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {ℓ ε : ℝ}

theorem ShiOptRates.Spider.step_decrease (hQ : QuadUpper f g ℓ) (hℓ : 0 < ℓ) (hε : 0 < ε) {x v : E}
    (herr : ‖v - g x‖ ≤ ε) (hbig : 2 * ε < ‖v‖) :
    f (x - (ε / ℓ) • (‖v‖⁻¹ • v)) ≤ f x - ε ^ 2 / (2 * ℓ) := by sorry
