-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_Supplement_corollary_4_3
-- name    : UnconditionalKLS.Dunkl.Supplement.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:18:04.822387+00:00
-- url     : https://prove2.me/theorems/97be6c5d-2fb9-4bda-b0bc-8e6dc45cb9a9
-- title:
--   Corollary 4.3 — $C_P(\eta)\le\frac13\max_j\mathbb E_\eta[(1+X_j)^4]$ on the positive orthant
-- statement:
--   Let $\eta$ be as in Proposition 4.2: the probability measure on $\mathbb R^n_+=(0,\infty)^n$ with density proportional to $e^{-V}$, where $V\in C^2(\mathbb R^n_+)$ is convex and $\partial_jV\ge0$ on $\mathbb R^n_+$ for every $j$. Then, for $X\sim\eta$,
--
--   $$C_P(\eta)\le\frac13\max_{j\in[n]}\mathbb E_\eta\big[(1+X_j)^4\big].$$
--
--   No absolute value is needed since $X_j>0$. Applied to the image $\mu_+$ of an unconditional log-concave measure, this gives the second summand in Theorem 1.3.
--
--   **Formalization Note** Expectations are $[0,\infty]$-valued lower integrals, so the bound is meaningful (and trivially true) when a fourth moment diverges; the factor $\frac13$ is in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: η a probability measure on ℝⁿ₊ with density proportional to e^{-V}, V ∈ C²(ℝⁿ₊) → V : ℝⁿ → ℝ, C² and convex on the open orthant, η = Z_V⁻¹·1_{ℝⁿ₊}e^{-V}dx with the hypothesis Z_V ≠ ∞; reason: "probability measure with density proportional to" needs a finite normalizer; Z_V > 0 is automatic; values of V off the orthant are irrelevant
--   - encoding: ∂_jV ≥ 0 → the base Fréchet partial d V j x ≥ 0 for x ∈ ℝⁿ₊; reason: V is differentiable on the open orthant
--   - encoding: (1/3) max_{j∈[n]} 𝔼_η[(1+X_j)⁴] → (1/3 : ℝ≥0∞) · ⨆ over j : Fin n of ∫⁻ ofReal((1+x_j)⁴) dη; reason: nonnegative integrand; a divergent expectation is +∞; for n = 0 the supremum is 0
--   - encoding: C_P(·), the best constant in (1.1) → the base `poincare` in ℝ≥0∞ (ambient locally Lipschitz tests on ℝⁿ, +∞ if no finite constant works); reason: same value whenever the constant is finite; +∞ otherwise
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 31, Corollary 4.3; proof p. 31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Supplement_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl.Supplement
open UnconditionalKLS.Dunkl
/-- Corollary 4.3, p. 31. -/
theorem corollary_4_3 {n : ℕ} (V : Fn n) (hV : ContDiffOn ℝ 2 V posOrthant)
    (hV_convex : ConvexOn ℝ posOrthant V)
    (hV_mono : ∀ j : Fin n, ∀ x ∈ posOrthant, 0 ≤ d V j x)
    (hZ : orthantNormalizer V ≠ ⊤) :
    poincare (orthantLaw V) ≤
      (1 / 3 : ℝ≥0∞) * ⨆ j : Fin n, ∫⁻ x, ENNReal.ofReal ((1 + x j) ^ 4) ∂orthantLaw V := by sorry
end UnconditionalKLS.Dunkl.Supplement
