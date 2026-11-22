-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_sgd_expectedDescent
-- name    : ShiOptRates.Stochastic.sgd_expectedDescent
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:50:13.79773+00:00
-- url     : https://prove2.me/theorems/b66ebbe2-e197-4e64-a0fa-089f93ab9104
-- title:
--   The SGD expected-descent recursion, derived from the oracle contract at any stepsize $0<h\le 1/L$
-- statement:
--   This theorem derives the one-step recursion that drives every stochastic-gradient rate, from nothing but the descent-lemma inequality and two oracle-contract identities.
--
--   Let $E$ be a real inner-product space, $f : E \to \mathbb R$ with gradient field $g : E \to E$ satisfying the quadratic upper bound with constant $L>0$,
--   $$f(y) \le f(x) + \langle g(x), y-x\rangle + \tfrac{L}{2}\|y-x\|^{2},$$
--   and let $(\Omega,\mu)$ be a probability space with a filtration $(\mathcal F_k)$. Let $x_k, \hat g_k : \Omega \to E$ be the iterates and oracle answers, fix a horizon $K$, a stepsize $h$ with $0 < h \le 1/L$, and a noise level $\sigma$. Assume
--
--   1. **Update rule.** $x_{k+1} = x_k - h\,\hat g_k$ for every $k<K$ and every sample point;
--   2. **Adaptedness.** $g(x_k)$ is $\mathcal F_k$-measurable for $k<K$;
--   3. **Oracle contract, first moment.** $\mathbb E[\hat g_k \mid \mathcal F_k] = g(x_k)$ almost surely;
--   4. **Oracle contract, second moment.** $\mathbb E\big[\|\hat g_k\|^{2} \mid \mathcal F_k\big] \le \|g(x_k)\|^{2} + \sigma^{2}$ almost surely;
--   5. Integrability side conditions on $\hat g_k$, $\|\hat g_k\|^{2}$, $f(x_k)$, $\|g(x_k)\|^{2}$, and $\langle g(x_k),\hat g_k\rangle$.
--
--   Write $a_k = \mathbb E[f(x_k)]$ and $b_k = \mathbb E\big[\|g(x_k)\|^{2}\big]$. The conclusion is that the pair $(a,b)$ satisfies the *expected-descent* recursion at parameters $(h,L,\sigma,K)$, namely
--
--   $$
--   a_{k+1} \;\le\; a_k \;-\; \frac{h}{2}\, b_k \;+\; \frac{L h^{2}\sigma^{2}}{2}\qquad\text{for every }k<K.
--   $$
--
--   Each iteration therefore buys $\tfrac{h}{2} b_k$ of objective decrease and pays a fixed noise tax $\tfrac{1}{2}Lh^{2}\sigma^{2}$; balancing the two is what fixes the stepsize and produces the $\varepsilon^{-4}$ horizon downstream.
--
--   The design point is the separation of concerns. `ExpectedDescent` is a predicate on two real sequences, so the rate theorem that consumes it is indifferent to how the recursion was obtained; this theorem is the bridge that obtains it from an actual trajectory. Notably, every hypothesis above is either the descent-lemma inequality, an integrability side condition, or one of the two oracle-contract identities — no hypothesis is itself a rate, and the tower property is derived rather than assumed. Substituting a different oracle contract at this interface is precisely how the library reaches inexact and quantum rates from the same downstream arithmetic.
--
--   **Formalization Note** Conditional expectations are Mathlib's, taken with respect to a `Filtration ℕ`, and the two contract hypotheses are almost-everywhere statements (an equality of functions for the first moment, an almost-everywhere inequality for the second). The conclusion is stated in terms of integrals of $f(x_k)$ and $\|g(x_k)\|^{2}$, i.e. expectations, not pathwise quantities.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/SGD.lean#L42-L120 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/SGD.lean
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
import Theorems.Thm_ShiOptRates_Stochastic_integral_inner_condExp
import Theorems.Thm_ShiOptRates_Stochastic_integral_le_of_condExp_le
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
# L3 / GL3 — SGD over an adaptive filtration

The layer the plan flagged as the hardest: the stochastic gradient at step `k` depends on
`x k`, which depends on all previous noise, so the analysis lives over a filtration and the
oracle contract is conditional.

The chain assembled here is:

`pathwise descent lemma` → `integrate` → `tower property (Bridge)` → `ExpectedDescent
(Recursion)` → `ε⁻⁴`.

The only genuinely martingale-theoretic step is the tower property, and it is discharged
by `integral_inner_condExp`: the `F_k`-measurable factor `∇f(xₖ)` is replaced by its
conditional expectation inside the inner product, turning the cross term
`E⟪∇f(xₖ), gₖ⟫` into `E‖∇f(xₖ)‖²`.

## Main results

* `sgd_expectedDescent` — an SGD trajectory's `(E f(xₖ), E‖∇f(xₖ)‖²)` satisfies
  `ExpectedDescent`.
* `sgd_rate` — **GL3**: `K ≥ 8 L Δ₀ σ² / ε⁴` iterations at stepsize `ε²/(2Lσ²)` give an
  iterate with `E‖∇f(xₖ)‖² ≤ ε²`.  The Ghadimi–Lan `ε⁻⁴`, with the constant explicit.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Filter Finset
open scoped InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {g : E → E} {L σ hstep : ℝ}

theorem ShiOptRates.Stochastic.sgd_expectedDescent (hQ : QuadUpper f g L) (hL : 0 < L)
    (hs : 0 < hstep) (hsL : hstep ≤ 1 / L)
    (ℱ : Filtration ℕ mΩ) (x gd : ℕ → Ω → E) (K : ℕ)
    (hxstep : ∀ k, k < K → ∀ ω, x (k + 1) ω = x k ω - hstep • gd k ω)
    (hadapt : ∀ k, k < K → AEStronglyMeasurable[ℱ k] (fun ω => g (x k ω)) μ)
    (hgint : ∀ k, k < K → Integrable (gd k) μ)
    (hg2 : ∀ k, k < K → Integrable (fun ω => ‖gd k ω‖ ^ 2) μ)
    (hfint : ∀ k, k ≤ K → Integrable (fun ω => f (x k ω)) μ)
    (hgradint : ∀ k, k < K → Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ)
    (hcross : ∀ k, k < K → Integrable (fun ω => ⟪g (x k ω), gd k ω⟫_ℝ) μ)
    (hunb : ∀ k, k < K → μ[gd k | ℱ k] =ᵐ[μ] fun ω => g (x k ω))
    (hsm : ∀ k, k < K →
      μ[fun ω => ‖gd k ω‖ ^ 2 | ℱ k] ≤ᵐ[μ] fun ω => ‖g (x k ω)‖ ^ 2 + σ ^ 2) :
    ExpectedDescent (fun k => ∫ ω, f (x k ω) ∂μ)
      (fun k => ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) hstep L σ K := by sorry
