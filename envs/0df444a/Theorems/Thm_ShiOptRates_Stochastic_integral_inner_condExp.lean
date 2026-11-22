-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_integral_inner_condExp
-- name    : ShiOptRates.Stochastic.integral_inner_condExp
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:28:28.901394+00:00
-- url     : https://prove2.me/theorems/2f827d6c-42de-4ac1-aed2-5d1c3050635d
-- title:
--   Tower property inside an inner product: $\int \langle e,\xi\rangle = \int \langle e, \mathbb E[\xi\mid m]\rangle$
-- statement:
--   This lemma is the tower-property step in its general vector-valued form: inside an integrated inner product, a factor measurable with respect to a sub-$\sigma$-algebra may be paired with the conditional expectation of the other factor.
--
--   Let $(\Omega,\mathcal M,\mu)$ be a measure space, $m \subseteq \mathcal M$ a sub-$\sigma$-algebra, and $E$ a real inner-product space. Let $e, \xi, \zeta : \Omega \to E$ and assume
--
--   1. $e$ is $m$-measurable (almost everywhere strongly measurable with respect to $m$);
--   2. $\xi$ is $\mu$-integrable, and the scalar product $\omega \mapsto \langle e(\omega), \xi(\omega)\rangle$ is $\mu$-integrable;
--   3. $\zeta$ is a version of the conditional expectation of $\xi$ given $m$, i.e. $\mathbb E[\xi \mid m] = \zeta$ almost everywhere.
--
--   Then
--
--   $$
--   \int_\Omega \langle e(\omega), \xi(\omega)\rangle \, d\mu(\omega) \;=\; \int_\Omega \langle e(\omega), \zeta(\omega)\rangle \, d\mu(\omega).
--   $$
--
--   This is the workhorse behind every cross-term computation in the stochastic part of the library. Along a stochastic-gradient trajectory the current point $x_k$ — and hence $g(x_k)$ — is $\mathcal F_k$-measurable while the oracle answer $\hat g_k$ is not, so the descent lemma's cross term $\int \langle g(x_k), \hat g_k\rangle$ must be rewritten using the oracle's first-moment contract $\mathbb E[\hat g_k \mid \mathcal F_k] = g(x_k)$. Isolating that manoeuvre as a standalone statement is what lets the SGD recursion be *derived* from the oracle contract rather than assumed: the tower property is never a hypothesis of a rate theorem in this library.
--
--   **Formalization Note** The hypotheses include the technical conditions Mathlib's conditional expectation requires: the sub-$\sigma$-algebra must be contained in the ambient one, and $\mu$ trimmed to it must be $\sigma$-finite. The conditional expectation is stated as an almost-everywhere equality with an explicit representative $\zeta$ rather than as a term, which is what makes the lemma directly applicable when the contract is given in that form. The result holds in any real inner-product space, via the bilinear pull-out of conditional expectation.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Bridge.lean#L57-L79 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

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

theorem ShiOptRates.Stochastic.integral_inner_condExp (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] {e ξ ζ : Ω → E}
    (he : AEStronglyMeasurable[m] e μ) (hξ : Integrable ξ μ)
    (hprod : Integrable (fun ω => ⟪e ω, ξ ω⟫_ℝ) μ)
    (hce : μ[ξ | m] =ᵐ[μ] ζ) :
    ∫ ω, ⟪e ω, ξ ω⟫_ℝ ∂μ = ∫ ω, ⟪e ω, ζ ω⟫_ℝ ∂μ := by sorry
