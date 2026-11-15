-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_Supplement_theorem_1_3
-- name    : UnconditionalKLS.Dunkl.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:18:37.003249+00:00
-- url     : https://prove2.me/theorems/5f64bb57-68e5-45e8-9f9c-db7547efa965
-- title:
--   Theorem 1.3 — $C_P(\mu)\le\max_j\mathbb E_\mu[X_j^2]+\frac13\max_j\mathbb E_\mu[(1+|X_j|)^4]$ for unconditional log-concave $\mu$
-- statement:
--   Let $\mu$ be an unconditional log-concave probability measure on $\mathbb R^n$: it has density $e^{-V}$ with $V:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ convex and invariant under each reflection $x_j\mapsto-x_j$. Then, for $X\sim\mu$,
--
--   $$C_P(\mu)\le\max_{j\in[n]}\mathbb E_\mu[X_j^2]+\frac13\max_{j\in[n]}\mathbb E_\mu\big[(1+|X_j|)^4\big].$$
--
--   The theorem covers every such measure, including uniform measures on unconditional convex bodies, with no smoothness, positivity, isotropy or moment assumption. When $\mu$ is in addition isotropic the right side is bounded by a universal constant, which gives the paper's main theorem (Theorem 1.1) with an explicit constant.
--
--   **Formalization Note** The arithmetic is in $[0,\infty]$: the moments are lower integrals and may a priori be $+\infty$; for $n=0$ both maxima are $0$.
--
--   Differences from the source:
--   - encoding: an unconditional log-concave probability measure μ on ℝⁿ (density e^{-V}, V : ℝⁿ → ℝ ∪ {∞} convex and unconditional) → the law of a published base `Potential n` (WithTop ℝ-valued potential with convex epigraph, invariant under each coordinate reflection, ∫ e^{-V} = 1, e^{-∞} = 0); reason: this is the paper's §1 definition verbatim; no smoothness, positivity or moment condition is added
--   - encoding: C_P(·), the best constant in (1.1) → the base `poincare` in ℝ≥0∞ (ambient locally Lipschitz tests on ℝⁿ, +∞ if no finite constant works); reason: same value whenever the constant is finite; +∞ otherwise
--   - encoding: max_{j∈[n]} 𝔼_μ[X_j²] → ⨆ over j : Fin n of ∫⁻ ofReal(x_j²) dμ in ℝ≥0∞; reason: nonnegative integrands, so the lintegral equals the expectation and a divergent one is +∞; for n = 0 the empty supremum is 0
--   - encoding: (1/3) max_{j∈[n]} 𝔼_μ[(1+|X_j|)⁴] → (1/3 : ℝ≥0∞) · ⨆ over j : Fin n of ∫⁻ ofReal((1+|x_j|)⁴) dμ; reason: nonnegative integrand; for n = 0 the supremum is 0
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 7, Theorem 1.3, (1.8); proof p. 31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Supplement_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl.Supplement
open UnconditionalKLS.Dunkl
/-- Theorem 1.3, p. 7, (1.8): every unconditional log-concave law, nonsmooth included. -/
theorem theorem_1_3 {n : ℕ} (V : Potential n) :
    poincare V.law ≤
      (⨆ j : Fin n, ∫⁻ x, ENNReal.ofReal ((x j) ^ 2) ∂V.law) +
        (1 / 3 : ℝ≥0∞) * ⨆ j : Fin n, ∫⁻ x, ENNReal.ofReal ((1 + |x j|) ^ 4) ∂V.law := by sorry
end UnconditionalKLS.Dunkl.Supplement
