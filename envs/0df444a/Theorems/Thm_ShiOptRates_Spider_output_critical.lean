-- Prove2me | Theorems.Thm_ShiOptRates_Spider_output_critical
-- name    : ShiOptRates.Spider.output_critical
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T23:03:50.991864+00:00
-- url     : https://prove2.me/theorems/4cdda0f5-34a3-4d3f-af22-70dc8f883026
-- title:
--   SPIDER correctness: a normalized-step trajectory reaches a $3\varepsilon$-critical point within $2\ell\Delta_0/\varepsilon^2$ steps
-- statement:
--   Let $E$ be a real inner-product space, let $f : E \to \mathbb{R}$ be an objective function and let $g : E \to E$ play the role of its gradient, $g = \nabla f$. Assume $f$ satisfies the *quadratic upper bound* (descent-lemma inequality) with constant $\ell > 0$,
--
--   $$
--   f(y) \;\le\; f(x) + \langle g(x),\, y - x\rangle + \frac{\ell}{2}\,\lVert y - x\rVert^{2}
--   \qquad \text{for all } x, y \in E,
--   $$
--
--   which is the only consequence of $\ell$-smoothness used here.
--
--   Fix an accuracy parameter $\varepsilon > 0$, a horizon $T \in \mathbb{N}$, and two sequences $(x_t)_{t \in \mathbb{N}}$ of iterates and $(v_t)_{t \in \mathbb{N}}$ of gradient estimates in $E$. Let $f^{\star} \in \mathbb{R}$ be a value with $f^{\star} \le f(x_T)$ (a lower bound on the objective at the final iterate is all that is needed; global boundedness below is not assumed), and write $\Delta_0 = f(x_0) - f^{\star}$ for the initial objective gap. Suppose:
--
--   1. **Normalized step.** For every $t < T$,
--   $$
--   x_{t+1} \;=\; x_t - \frac{\varepsilon}{\ell}\cdot \frac{v_t}{\lVert v_t\rVert},
--   $$
--   so each step has length $\varepsilon/\ell$ and moves along the direction of the estimate $v_t$ only.
--   2. **Oracle accuracy.** For every $t < T$, the estimate is $\varepsilon$-accurate, $\lVert v_t - g(x_t)\rVert \le \varepsilon$.
--   3. **Long enough horizon.** $\displaystyle \frac{2\,\ell\,\Delta_0}{\varepsilon^{2}} < T$.
--
--   Then some iterate visited before the horizon is $3\varepsilon$-critical:
--
--   $$
--   \exists\, t < T,\qquad \lVert g(x_t)\rVert \;\le\; 3\varepsilon .
--   $$
--
--   This is the correctness half of the SPIDER-style normalized-step method, stated pathwise: no probability appears, because randomness enters only through the accuracy hypothesis (2), which here is assumed to hold on the trajectory. Rescaling $\varepsilon \mapsto \varepsilon/3$ turns the conclusion into an honest $\varepsilon$-critical point reached within $18\,\ell\Delta_0/\varepsilon^{2}$ steps, a fully explicit constant that can be compared directly against the budget stated for the published algorithm. Making such constants visible, rather than absorbing them into $\widetilde{O}(\cdot)$, is the purpose of the surrounding library.
--
--   **Formalization Note** The gradient is carried as a separate function $g$ rather than as a differentiability hypothesis on $f$, so the statement is about the pair $(f, g)$ satisfying the quadratic upper bound; the step rule uses the Lean scalar-action notation and $\lVert v_t\rVert^{-1} \bullet v_t$ for the normalized direction, with no positivity hypothesis on $\lVert v_t\rVert$ imposed separately.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Spider.lean#L371-L394 (commit 4c0b84980914...) | Correctness of the SPIDER schedule's output (3-eps-critical within 2 l Delta_0 / eps^2). The related published statement is Fang et al.'s Theorem 1, which Sidford & Zhang (arXiv:2308.01582) import rather than reprove; the probabilistic wrapper at the random return time is NOT part of this theorem. | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_Spider_no_return_bound
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

theorem ShiOptRates.Spider.output_critical (hQ : QuadUpper f g ℓ) (hℓ : 0 < ℓ) (hε : 0 < ε) {fstar : ℝ}
    (x v : ℕ → E) (T : ℕ) (hlow : fstar ≤ f (x T))
    (hstep : ∀ t < T, x (t + 1) = x t - (ε / ℓ) • (‖v t‖⁻¹ • v t))
    (herr : ∀ t < T, ‖v t - g (x t)‖ ≤ ε)
    (hT : 2 * ℓ * (f (x 0) - fstar) / ε ^ 2 < (T : ℝ)) :
    ∃ t < T, ‖g (x t)‖ ≤ 3 * ε := by sorry
