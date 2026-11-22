-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_accumulation_sq_stopped
-- name    : ShiOptRates.Stochastic.accumulation_sq_stopped
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:58:14.870892+00:00
-- url     : https://prove2.me/theorems/1f5f1f1a-9163-4003-9a4a-b1c7210960f0
-- title:
--   Second-moment accumulation law for a martingale-difference recursion stopped at a random time
-- statement:
--   Let $(\Omega, \mathcal{F}, \mu)$ be a finite measure space carrying a filtration $(\mathcal{F}_k)_{k \in \mathbb{N}}$, and let $E$ be a real Hilbert space. Consider two $E$-valued processes $s = (s_k)$ and $\xi = (\xi_k)$ and a random time $\tau : \Omega \to \mathbb{N}$. Write the *stopped increment*
--
--   $$
--   Z_k(\omega) \;=\; \mathbf{1}\{k < \tau(\omega)\}\,\xi_k(\omega),
--   $$
--
--   i.e. the increment $\xi_k$ while the process is still running and $0$ once it has stopped. Assume the accumulated error follows the recursion
--
--   $$
--   s_{k+1}(\omega) \;=\; s_k(\omega) + Z_k(\omega) \qquad \text{for all } k,\ \omega,
--   $$
--
--   that each increment is a martingale difference, $\mathbb{E}[\xi_k \mid \mathcal{F}_k] = 0$ almost surely, that the $\mathcal{F}_k$-measurable factor $\mathbf{1}\{k<\tau\}\,s_k$ is (a.e. strongly) $\mathcal{F}_k$-measurable, and that the increments have uniformly bounded second moment,
--
--   $$
--   \mathbb{E}\,\lVert \xi_k \rVert^{2} \;\le\; \delta^{2} \qquad \text{for all } k,
--   $$
--
--   together with the integrability needed for each expectation below to make sense. Then for every horizon $K \in \mathbb{N}$,
--
--   $$
--   \mathbb{E}\,\lVert s_K \rVert^{2} \;\le\; \mathbb{E}\,\lVert s_0 \rVert^{2} \;+\; K\,\delta^{2}.
--   $$
--
--   Here $\delta \ge 0$ is the per-step noise level, $s_0$ the initial error, and $K$ the number of steps; the bound grows only linearly in $K$, so the root-mean-square error grows like $\sqrt{K}\,\delta$ rather than $K\delta$ — this is the gain that orthogonality of the increments buys over a triangle-inequality accounting.
--
--   The role of the result is to extend the fixed-horizon accumulation law to a *random* return time, which is what recursive variance-reduced estimators such as SPIDER actually use: the algorithm stops when its gradient estimate becomes small, and that time is data-dependent. The constant is identical to the unstopped law, reflecting that stopping can only remove increments, never add them.
--
--   **Formalization Note** The stopped increment and the $\mathcal{F}_k$-measurable prefactor appear as the definitions `stoppedIncr` and `stoppedFactor`. Because Lean's Bochner integral requires integrability as an explicit side condition, the statement carries separate integrability hypotheses for $\lVert s_k \rVert^2$, $\lVert \xi_k \rVert^2$, $\lVert Z_k \rVert^2$, the inner products $\langle s_k, Z_k \rangle$ and $\langle \mathbf{1}\{k<\tau\}s_k, \xi_k \rangle$, and for $\xi_k$ itself. The measure is only assumed finite, not normalized.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Stopped.lean#L72-L98 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Stopped.lean
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
import Definitions.Def_ShiOptrates_Stochastic_Stopped
import Theorems.Thm_ShiOptRates_Stochastic_accumulation_sq
import Theorems.Thm_ShiOptRates_Stochastic_integral_inner_eq_zero_of_condExp_eq_zero
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
# The accumulation law at a stopped time

`accumulation_sq` bounds `E‖e_K‖²` at a *fixed* index `K`.  Algorithms that stop
adaptively — SPIDER returns as soon as `‖vₜ‖ ≤ 2ε` — need the bound at the **random** index
`τ`, and the naive route fails: conditioning on `{τ = k}` destroys the unconditional
variance bound, which is exactly why `Spider.output_critical` is stated pathwise and why
Sidford–Zhang import Fang et al.'s Theorem 1 rather than reproving it.

The fix is to stop the process rather than the bound.  Write

`s_k = e_{τ ∧ k}`,  so that  `s_{k+1} = s_k + 1_{k < τ} ξ_k`,

and observe that `1_{k < τ} s_k` is still `ℱ_k`-measurable, so the *same* pull-out
(`integral_inner_condExp`) gives orthogonality of the stopped increments.  Then
`accumulation_sq` applies verbatim and the constant does not change:

`E‖e_{τ∧K}‖² ≤ E‖e_0‖² + K δ².`

## Main results

* `stopped_orthogonal` — the stopped increments inherit `L²` orthogonality.
* `accumulation_sq_stopped` — the accumulation law at a stopped time, same constant.
* `stopped_eq_of_le` — `s K = e_τ` when `τ ≤ K`, so the bound is about `e_τ` itself.
* `prob_stopped_error_large_le` — Markov: the accuracy event
  `‖e_τ‖ ≤ ε` fails with probability at most `(E‖e_0‖² + K δ²)/ε²`.  This is what feeds
  `Spider.output_critical`'s hypothesis.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Filter
open scoped InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem ShiOptRates.Stochastic.accumulation_sq_stopped [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {s ξ : ℕ → Ω → E} {τ : Ω → ℕ} {δ : ℝ} (K : ℕ)
    (hsrec : ∀ k ω, s (k + 1) ω = s k ω + stoppedIncr ξ τ k ω)
    (hsin : ∀ k, Integrable (fun ω => ‖s k ω‖ ^ 2) μ)
    (hxin : ∀ k, Integrable (fun ω => ‖ξ k ω‖ ^ 2) μ)
    (hzin : ∀ k, Integrable (fun ω => ‖stoppedIncr ξ τ k ω‖ ^ 2) μ)
    (hcin : ∀ k, Integrable (fun ω => ⟪s k ω, stoppedIncr ξ τ k ω⟫_ℝ) μ)
    (hfac : ∀ k, AEStronglyMeasurable[ℱ k] (stoppedFactor s τ k) μ)
    (hxint : ∀ k, Integrable (ξ k) μ)
    (hprod : ∀ k, Integrable (fun ω => ⟪stoppedFactor s τ k ω, ξ k ω⟫_ℝ) μ)
    (hmart : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    (hbnd : ∀ k, ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ ≤ δ ^ 2) :
    ∫ ω, ‖s K ω‖ ^ 2 ∂μ ≤ (∫ ω, ‖s 0 ω‖ ^ 2 ∂μ) + K * δ ^ 2 := by sorry
