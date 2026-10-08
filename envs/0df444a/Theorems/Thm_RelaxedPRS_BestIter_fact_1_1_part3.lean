-- Prove2me | Theorems.Thm_RelaxedPRS_BestIter_fact_1_1_part3
-- name    : RelaxedPRS.BestIter.fact_1_1_part3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:17.346023+00:00
-- url     : https://prove2.me/theorems/b85c4d69-3fc2-4842-a2d8-93d587a3b223
-- title:
--   Fact 1.1 Part 3, p. 6 — the best entry of a summable sequence: nonincreasing, ≤ (Σλ_i a_i)/Λ_k, and o(1/(Λ_k − Λ_⌈k/2⌉))
-- statement:
--   Let $(\lambda_j)_{j\ge0}$ and $(a_j)_{j\ge0}$ be nonnegative real sequences with $\sum_{i=0}^\infty \lambda_i a_i < \infty$, let $\Lambda_k = \sum_{i=0}^k \lambda_i$, and let $a_{k_{\mathrm{best}}} = \min_{i = 0, \dots, k} a_i$. Then
--   1. $(a_{k_{\mathrm{best}}})_{k\ge0}$ is nonincreasing;
--   2. for every $k \ge 0$, $\Lambda_k\, a_{k_{\mathrm{best}}} \le \sum_{i=0}^\infty \lambda_i a_i$, i.e. $a_{k_{\mathrm{best}}} \le \frac{1}{\Lambda_k}\sum_{i=0}^\infty \lambda_i a_i$ whenever $\Lambda_k > 0$;
--   3. if moreover $\lambda_j \ge c$ for all $j$ and some $c > 0$, then
--   $$a_{k_{\mathrm{best}}} = o\Big(\frac{1}{\Lambda_k - \Lambda_{\lceil k/2\rceil}}\Big) \qquad (k \to \infty).$$
--
--   This is the device that converts a summable bound into a rate for the best iterate when monotonicity of the sequence itself is not available.
--
--   **Formalization Note** The bound in item 2 is stated in multiplied form, which is equivalent when $\Lambda_k > 0$ and avoids dividing by zero otherwise. The little-o in item 3 is stated under the additional hypothesis that $\lambda_j$ is bounded below by a positive constant: as printed, with $\lambda \equiv 0$ the denominator $\Lambda_k - \Lambda_{\lceil k/2\rceil}$ vanishes for every $k$ and the claim is meaningless. Every use in the paper has $\lambda_j$ bounded away from $0$ (here $\lambda_j \ge \underline\tau > 0$). $\lceil k/2\rceil$ is written as the natural-number quotient $(k+1)/2$. Part 2 of Fact 1.1 (faster rates) is not part of this item.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 6, Fact 1.1 Parts 1 and 3, (1.7); (1.3)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace RelaxedPRS.BestIter

theorem fact_1_1_part3 (lam a : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j) (ha : ∀ j, 0 ≤ a j)
    (hsum : Summable (fun i => lam i * a i)) :
    Antitone (fun k : ℕ => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a) ∧
    (∀ k : ℕ, RelaxedPRS.StrongCvx.Lam lam k * (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a ≤
      ∑' i, lam i * a i) ∧
    ((∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ lam j) →
      (fun k : ℕ => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a) =o[atTop]
        (fun k : ℕ => 1 / (RelaxedPRS.StrongCvx.Lam lam k - RelaxedPRS.StrongCvx.Lam lam ((k + 1) / 2)))) := by sorry

end RelaxedPRS.BestIter
