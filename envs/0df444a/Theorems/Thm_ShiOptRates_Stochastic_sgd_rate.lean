-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_sgd_rate
-- name    : ShiOptRates.Stochastic.sgd_rate
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T23:04:19.27227+00:00
-- url     : https://prove2.me/theorems/382af5c3-af35-4b11-ac1d-13448b609ee3
-- title:
--   SGD on a smooth nonconvex objective: $K \ge 8L\Delta_0\sigma^2/\varepsilon^4$ suffices
-- statement:
--   This is the Ghadimi–Lan $\varepsilon^{-4}$ complexity bound for stochastic gradient descent on a smooth nonconvex objective, stated over a genuine adaptive filtration and with the constant $8$ exhibited rather than absorbed into an $O(\cdot)$.
--
--   Let $E$ be a real inner-product space, $f : E \to \mathbb R$ an objective with gradient field $g : E \to E$, and suppose $f$ satisfies the quadratic upper bound (descent-lemma inequality) with constant $L>0$:
--   $$f(y) \le f(x) + \langle g(x),\, y-x\rangle + \tfrac{L}{2}\|y-x\|^{2}\qquad\text{for all }x,y.$$
--   Let $(\Omega,\mu)$ be a probability space carrying a filtration $(\mathcal F_k)_{k\in\mathbb N}$, let $x_k : \Omega \to E$ be the iterates and $\hat g_k : \Omega \to E$ the oracle outputs, and fix $\sigma>0$, $\varepsilon>0$ with $\varepsilon^{2}\le 2\sigma^{2}$.
--
--   The hypotheses are:
--
--   1. **Update rule.** $x_{k+1} = x_k - \dfrac{\varepsilon^{2}}{2L\sigma^{2}}\,\hat g_k$ for every $k<K$ — a constant stepsize $h = \varepsilon^{2}/(2L\sigma^{2})$.
--   2. **Adaptedness.** $g(x_k)$ is $\mathcal F_k$-measurable for $k<K$.
--   3. **Oracle contract, first moment.** $\mathbb E[\hat g_k \mid \mathcal F_k] = g(x_k)$ almost surely: the oracle is conditionally unbiased.
--   4. **Oracle contract, second moment.** $\mathbb E\big[\|\hat g_k\|^{2}\,\big|\,\mathcal F_k\big] \le \|g(x_k)\|^{2} + \sigma^{2}$ almost surely.
--   5. **Lower bound.** $f^\star \le \mathbb E[f(x_K)]$, together with the initial gap $\Delta_0 = \mathbb E[f(x_0)] - f^\star$.
--   6. **Horizon.** $K>0$ and $\;8L\Delta_0\sigma^{2}/\varepsilon^{4} \le K$.
--   7. Integrability side conditions on $\hat g_k$, $\|\hat g_k\|^{2}$, $f(x_k)$, $\|g(x_k)\|^{2}$, and $\langle g(x_k),\hat g_k\rangle$.
--
--   Under these hypotheses some iterate before the horizon is $\varepsilon$-stationary in mean square:
--
--   $$
--   \exists\, k < K \quad\text{such that}\quad \mathbb E\big[\|g(x_k)\|^{2}\big] \;\le\; \varepsilon^{2}.
--   $$
--
--   The statement is the stochastic counterpart of the exact-gradient $\varepsilon^{-2}$ rate: replacing the deterministic gradient by a conditionally unbiased oracle of bounded conditional second moment moves the complexity from $\varepsilon^{-2}$ to $\varepsilon^{-4}$, and the theorem pins the prefactor at exactly $8L\Delta_0\sigma^{2}$. Because the stepsize is *supplied and verified* rather than optimized inside the proof, the same statement can be reused verbatim under different oracle contracts and cost models, which is how the library derives classical, inexact, and quantum query bills from one rate.
--
--   **Formalization Note** The oracle contract is stated with Mathlib's conditional expectation with respect to a `Filtration`, so the tower property used along the trajectory is a consequence of the hypotheses rather than an extra assumption; the conclusion is about the integral of $\|g(x_k)\|^{2}$, i.e. the expectation, not a pathwise bound. The condition $\varepsilon^{2}\le 2\sigma^{2}$ keeps the prescribed stepsize admissible, $h \le 1/L$.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/SGD.lean#L122-L150 (commit 4c0b84980914...) | The eps^-4 rate for smooth nonconvex SGD, due to Ghadimi & Lan (2013). | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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
import Theorems.Thm_ShiOptRates_Stochastic_exists_le_sq_of_stepsize
import Theorems.Thm_ShiOptRates_Stochastic_sgd_expectedDescent
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

theorem ShiOptRates.Stochastic.sgd_rate (hQ : QuadUpper f g L) (hL : 0 < L) {σ ε fstar : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) (hεσ : ε ^ 2 ≤ 2 * σ ^ 2)
    (ℱ : Filtration ℕ mΩ) (x gd : ℕ → Ω → E) (K : ℕ) (hK : 0 < K)
    (hxstep : ∀ k, k < K → ∀ ω, x (k + 1) ω = x k ω - (ε ^ 2 / (2 * L * σ ^ 2)) • gd k ω)
    (hadapt : ∀ k, k < K → AEStronglyMeasurable[ℱ k] (fun ω => g (x k ω)) μ)
    (hgint : ∀ k, k < K → Integrable (gd k) μ)
    (hg2 : ∀ k, k < K → Integrable (fun ω => ‖gd k ω‖ ^ 2) μ)
    (hfint : ∀ k, k ≤ K → Integrable (fun ω => f (x k ω)) μ)
    (hgradint : ∀ k, k < K → Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ)
    (hcross : ∀ k, k < K → Integrable (fun ω => ⟪g (x k ω), gd k ω⟫_ℝ) μ)
    (hunb : ∀ k, k < K → μ[gd k | ℱ k] =ᵐ[μ] fun ω => g (x k ω))
    (hsm : ∀ k, k < K →
      μ[fun ω => ‖gd k ω‖ ^ 2 | ℱ k] ≤ᵐ[μ] fun ω => ‖g (x k ω)‖ ^ 2 + σ ^ 2)
    (hlow : fstar ≤ ∫ ω, f (x K ω) ∂μ)
    (hKbig : 8 * L * ((∫ ω, f (x 0 ω) ∂μ) - fstar) * σ ^ 2 / ε ^ 4 ≤ (K : ℝ)) :
    ∃ k < K, ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ ≤ ε ^ 2 := by sorry
