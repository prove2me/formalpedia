-- Prove2me | Theorems.Thm_RiskUncSets_Symmetric_mixture_mem_restrictedSimplex
-- name    : RiskUncSets.Symmetric.mixture_mem_restrictedSimplex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:41.87796+00:00
-- url     : https://prove2.me/theorems/d6d844d3-c7ab-4b21-900d-a25dae61288a
-- title:
--   Proof of Theorem 4.4, equation (11): mixtures of generators lie in the restricted simplex
-- statement:
--   Let $N\ge1$ and $\widehat N=\lfloor N/2\rfloor+1$. Choose nonnegative coefficients $\lambda_1,\ldots,\lambda_{\widehat N}$ summing to one, and let $\bar q^{j}$ be the vectors in equation (10). Then their mixture
--
--   $$
--   q=\sum_{j=1}^{\widehat N}\lambda_j\bar q^{j}
--   \quad\text{belongs to }\widehat\Delta^N.
--   $$
--
--   Thus the proposed generators and all their convex mixtures remain valid nonincreasing probability weights.
--
--   **Formalization Note** The result holds for both odd and even $N$; the printed calculation writes out the odd case and says the even case is analogous. Indices in Lean start at zero.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1491, proof of Theorem 4.4, equation (11); DOI 10.1287/opre.1080.0646

import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem mixture_mem_restrictedSimplex {N : ℕ} (hN : 0 < N)
    (lam : Fin (Nhat N) → ℝ) (h0 : ∀ j, 0 ≤ lam j)
    (h1 : ∑ j, lam j = 1) :
    (∑ j, lam j • qbar j) ∈ restrictedSimplex N := by sorry

end RiskUncSets.Symmetric
