-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_integral_inner_eq_zero_of_condExp_eq_zero
-- name    : ShiOptRates.Stochastic.integral_inner_eq_zero_of_condExp_eq_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:49:42.92989+00:00
-- url     : https://prove2.me/theorems/5043ab8d-f158-4101-b980-1d0589745422
-- title:
--   A martingale difference is $L^{2}$-orthogonal to the past: $\mathbb{E}\,\langle e, \xi\rangle = 0$ when $\mathbb{E}[\xi \mid \mathcal{G}] = 0$
-- statement:
--   Let $(\Omega, \mathcal{F}, \mu)$ be a measure space, let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-$\sigma$-algebra, and let $E$ be a real inner-product space. Let $e, \xi : \Omega \to E$ be two random vectors such that:
--
--   1. $e$ is (almost everywhere strongly) $\mathcal{G}$-measurable — it is determined by the past;
--   2. $\xi$ is integrable, and the scalar product $\omega \mapsto \langle e(\omega), \xi(\omega)\rangle$ is integrable;
--   3. $\xi$ is a **martingale difference** relative to $\mathcal{G}$: $\mathbb{E}[\xi \mid \mathcal{G}] = 0$ almost everywhere.
--
--   Then the two are orthogonal in $L^{2}$:
--
--   $$
--   \int_{\Omega} \langle e(\omega),\, \xi(\omega)\rangle \, \mathrm{d}\mu(\omega) \;=\; 0 .
--   $$
--
--   This identity is the workhorse behind variance-accumulation laws for recursive gradient estimators. When the estimator error obeys $e_{k+1} = e_k + \xi_k$ with each increment a martingale difference with respect to the past, the cross terms $\mathbb{E}\langle e_k, \xi_k\rangle$ vanish and the squared error grows *additively in the variance* — $\mathbb{E}\lVert e_K\rVert^{2} \le \mathbb{E}\lVert e_0\rVert^{2} + \sum_k \mathbb{E}\lVert \xi_k\rVert^{2}$, giving a $\sqrt{K}$ error rather than the $K$ error that a merely bounded-error oracle would force. That distinction is exactly what makes variance-reduced and quantum-accelerated rates go through, and it is why unbiasedness, rather than a bound on the error, is the oracle contract these analyses assume.
--
--   **Formalization Note** The statement uses Lean's measure-theoretic conditional expectation $\mu[\xi \mid \mathcal{G}]$, which requires the trimmed measure $\mu\!\restriction_{\mathcal{G}}$ to be $\sigma$-finite; both that instance and the inclusion $\mathcal{G} \le \mathcal{F}$ are explicit hypotheses. Finiteness of $\mu$ is not assumed. The measurability hypothesis on $e$ is stated with respect to $\mathcal{G}$, which is what licenses the pull-out step.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Bridge.lean#L81-L90 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Bridge.lean
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
# L3d — From a martingale difference to `L²` orthogonality

`Optrates.Stochastic.Accumulation` proves the `√K` accumulation law from an `L²`
orthogonality hypothesis, `∫ ⟪eₖ, ξₖ⟫ = 0`.  This file discharges that hypothesis from the
condition an actual stochastic algorithm satisfies: `ξₖ` is a martingale difference with
respect to a filtration to which `eₖ` is adapted.

This is the filtration layer the plan flagged as the likely sink.  It turns out to be
short, because Mathlib's `condExp_bilin_of_aestronglyMeasurable_left` already provides the
pull-out property for a general continuous bilinear map — so the vector-valued case needs
no more work than the scalar one, once the real inner product is packaged as such a map.

## Main definitions

* `innerBilin` — the real inner product as a continuous bilinear map, the form Mathlib's
  pull-out lemma consumes.

## Main results

* `integral_inner_eq_zero_of_condExp_eq_zero` — the tower-property step:
  `E[ξ | m] = 0` and `e` `m`-measurable give `E⟪e, ξ⟫ = 0`.
* `accumulation_sq_of_martingale` — **`√K` accumulation under a genuine filtration**:
  adapted error, martingale-difference increments, bounded conditional second moments.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Filter
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem ShiOptRates.Stochastic.integral_inner_eq_zero_of_condExp_eq_zero (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {e ξ : Ω → E}
    (he : AEStronglyMeasurable[m] e μ) (hξ : Integrable ξ μ)
    (hprod : Integrable (fun ω => ⟪e ω, ξ ω⟫_ℝ) μ)
    (hmart : μ[ξ | m] =ᵐ[μ] 0) :
    ∫ ω, ⟪e ω, ξ ω⟫_ℝ ∂μ = 0 := by sorry
