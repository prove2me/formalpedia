-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_accumulation_sq
-- name    : ShiOptRates.Stochastic.accumulation_sq
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:28:11.302354+00:00
-- url     : https://prove2.me/theorems/ab3940f4-ad0a-4563-9158-6a987a5d4c8b
-- title:
--   Unbiased increments accumulate linearly in the squared norm: $\mathbb E\|e_K\|^{2}\le \mathbb E\|e_0\|^{2}+K\delta^{2}$
-- statement:
--   This is the Itô-isometry / Pythagoras law for a recursively built error, in the form used by variance-reduced estimators.
--
--   Let $(\Omega,\mu)$ be a measure space and $E$ a real inner-product space. Let $e_k, \xi_k : \Omega \to E$ be two families of $E$-valued random variables satisfying the recursion
--   $$e_{k+1}(\omega) = e_k(\omega) + \xi_k(\omega)\qquad\text{for every }k\text{ and every }\omega,$$
--   so that $e_k$ is the accumulated error after $k$ increments and $\xi_k$ is the $k$-th increment. Fix $\delta$ and assume
--
--   1. **Orthogonality of increments.** $\displaystyle\int \langle e_k, \xi_k\rangle \, d\mu = 0$ for every $k$ — the increment is uncorrelated with the error already accumulated, which is what an unbiased (martingale-difference) oracle provides;
--   2. **Increment size.** $\displaystyle\int \|\xi_k\|^{2}\, d\mu \le \delta^{2}$ for every $k$;
--   3. Integrability of $\|e_k\|^{2}$, $\|\xi_k\|^{2}$, and $\langle e_k,\xi_k\rangle$ for every $k$.
--
--   Then for every horizon $K$,
--
--   $$
--   \int \|e_K\|^{2}\, d\mu \;\le\; \int \|e_0\|^{2}\, d\mu \;+\; K\,\delta^{2}.
--   $$
--
--   The content is the scaling law: the *squared* error grows only additively in $K$, so the error itself grows like $\sqrt K\,\delta$ rather than $K\delta$. This distinction is load-bearing. The library proves a companion statement, `accumulation_linear`, from the *same* recursion with the orthogonality hypothesis replaced by a pathwise bound on each increment, and there the conclusion is $\|e_K\| \le \|e_0\| + K\delta$. The only difference between the two error laws is which oracle contract supplies $\xi$ — an unbiasedness identity versus a deterministic error bound — which is exactly the library's thesis that the oracle should be a parameter. In the SPIDER analysis this $\sqrt K$-versus-$K$ gap is what makes the published epoch schedule feasible: with the bounded-error law the accumulated epoch error would be $(s_1+q s_2)^{2}$ instead of $s_1^{2}+q s_2^{2}$, and the rate would not follow.
--
--   **Formalization Note** No filtration, independence, or probability normalization is assumed: the hypotheses are stated directly as vanishing integrals of the cross terms, so the lemma applies whenever a martingale-difference structure has already been reduced to those identities. The bound is attained — the library exhibits a Rademacher witness for which equality holds at $K=1$ — so the constant is not slack.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Accumulation.lean#L92-L122 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Accumulation.lean
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
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3c — How errors accumulate in a recursive estimator

**The scientific content of the library.**  A recursive gradient estimator (SARAH, SPIDER,
STORM, and the variance-reduction family generally) has error obeying one recursion,

`e_{k+1} = e_k + ξ_k`,

and the whole question of whether such an estimator is worth building is: how does `‖e_k‖`
grow with `k`?  The answer depends *only* on which oracle supplies the increments `ξ_k`:

* **Bounded (deterministic) increments** — `‖ξ_k‖ ≤ δ` — accumulate **linearly**:
  `‖e_K‖ ≤ ‖e_0‖ + K δ`, and `accumulation_linear_tight` exhibits increments attaining it.
* **Unbiased increments** — orthogonal in `L²`, `E‖ξ_k‖² ≤ δ²` — accumulate as **√K**:
  `E‖e_K‖² ≤ E‖e_0‖² + K δ²`.

Same recursion, same `δ`, different oracle contract, and the exponent on `K` differs.
This is the fact that decides whether recursive variance reduction transfers to a
bounded-error (e.g. quantum) oracle, and it is exactly the kind of claim that should be
machine-checked rather than asserted: the linear bound is *tight*, so the loss is real and
not an artifact of a lossy proof.

## Main results

* `accumulation_linear` / `accumulation_linear_tight` — the deterministic law, and its
  tightness witness.
* `accumulation_sq` — the `L²` law under orthogonal increments.
* `separation_linear_vs_sqrt` — the two laws side by side, with the crossover.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Finset
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Bounded increments accumulate linearly -/

/-! ### Unbiased increments accumulate as `√K`

The hypothesis `horth` — that each increment is orthogonal in `L²` to the accumulated error
before it — is precisely what a martingale-difference sequence provides.  See
`Optrates.Stochastic.Bridge` for the derivation of `horth` from a conditional-expectation
hypothesis. -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [CompleteSpace E]
omit [IsProbabilityMeasure μ] [CompleteSpace E]

theorem ShiOptRates.Stochastic.accumulation_sq {e ξ : ℕ → Ω → E} {δ : ℝ} (K : ℕ)
    (hrec : ∀ k ω, e (k + 1) ω = e k ω + ξ k ω)
    (hein : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ 2) μ)
    (hxin : ∀ k, Integrable (fun ω => ‖ξ k ω‖ ^ 2) μ)
    (hcin : ∀ k, Integrable (fun ω => ⟪e k ω, ξ k ω⟫_ℝ) μ)
    (horth : ∀ k, ∫ ω, ⟪e k ω, ξ k ω⟫_ℝ ∂μ = 0)
    (hbnd : ∀ k, ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ ≤ δ ^ 2) :
    ∫ ω, ‖e K ω‖ ^ 2 ∂μ ≤ (∫ ω, ‖e 0 ω‖ ^ 2 ∂μ) + K * δ ^ 2 := by sorry
