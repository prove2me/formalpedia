-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_Supplement_lemma_4_1
-- name    : UnconditionalKLS.Dunkl.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:16:58.685914+00:00
-- url     : https://prove2.me/theorems/5850e49e-3334-4ac5-93e6-d95db90ffb98
-- title:
--   Lemma 4.1 — reduction to the positive orthant: $C_P(\mu)\le C_P(\mu_+)+\max_j\mathbb E_\mu[X_j^2]$
-- statement:
--   Let $\mu$ be an unconditional log-concave probability measure on $\mathbb R^n$: it has density $e^{-V}$ with $V:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ convex and invariant under each reflection $x_j\mapsto -x_j$. Let $X\sim\mu$ and let $\mu_+$ be the law of $(|X_1|,\dots,|X_n|)$. Then
--
--   $$C_P(\mu)\le C_P(\mu_+)+\max_{j\in[n]}\mathbb E_\mu[X_j^2].$$
--
--   The lemma reduces a Poincaré inequality for an unconditional measure to one for its image on the closed positive orthant, at the price of the largest coordinate second moment. It provides the first summand in Theorem 1.3.
--
--   **Formalization Note** The arithmetic is in $[0,\infty]$: both Poincaré constants and the moments may be $+\infty$, and for $n=0$ the maximum over the empty index set is $0$.
--
--   Differences from the source:
--   - encoding: an unconditional log-concave probability measure μ on ℝⁿ (density e^{-V}, V : ℝⁿ → ℝ ∪ {∞} convex and unconditional) → the law of a published base `Potential n` (WithTop ℝ-valued potential with convex epigraph, invariant under each coordinate reflection, ∫ e^{-V} = 1, e^{-∞} = 0); reason: this is the paper's §1 definition verbatim; no smoothness, positivity or moment condition is added
--   - encoding: C_P(·), the best constant in (1.1) → the base `poincare` in ℝ≥0∞ (ambient locally Lipschitz tests on ℝⁿ, +∞ if no finite constant works); reason: same value whenever the constant is finite; +∞ otherwise
--   - encoding: max_{j∈[n]} 𝔼_μ[X_j²] → ⨆ over j : Fin n of ∫⁻ ofReal(x_j²) dμ in ℝ≥0∞; reason: nonnegative integrands, so the lintegral equals the expectation and a divergent one is +∞; for n = 0 the empty supremum is 0
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 28, Lemma 4.1, (4.4); proof pp. 28–29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Supplement_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl.Supplement
open UnconditionalKLS.Dunkl
/-- Lemma 4.1, p. 28 (reduction to the positive orthant, (4.4)). -/
theorem lemma_4_1 {n : ℕ} (V : Potential n) :
    poincare V.law ≤
      poincare (plusLaw V.law) + ⨆ j : Fin n, ∫⁻ x, ENNReal.ofReal ((x j) ^ 2) ∂V.law := by sorry
end UnconditionalKLS.Dunkl.Supplement
