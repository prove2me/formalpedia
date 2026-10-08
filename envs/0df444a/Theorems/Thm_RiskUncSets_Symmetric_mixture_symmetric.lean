-- Prove2me | Theorems.Thm_RiskUncSets_Symmetric_mixture_symmetric
-- name    : RiskUncSets.Symmetric.mixture_symmetric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:55.85659+00:00
-- url     : https://prove2.me/theorems/b3efafeb-d1df-4324-9d76-7975a68e4710
-- title:
--   Proof of Theorem 4.4: mixtures satisfy the reversal symmetry condition
-- statement:
--   Let $N\ge1$ and let $q=\sum_{j=1}^{\widehat N}\lambda_j\bar q^{j}$ be a convex mixture of the generator vectors in equation (10). Reversing the coordinate order gives
--
--   $$
--   \frac{2}{N}-q_i=q_{N-i+1}\quad(1\le i\le N),
--   \qquad q\in\widehat\Delta^N_{\mathrm{sym}}.
--   $$
--
--   This is the forward inclusion from the convex hull of the generator columns into the symmetric restricted simplex.
--
--   **Formalization Note** Lean's `Fin.rev` is the one-based reversal $i\mapsto N-i+1$. The result includes membership in the restricted simplex, rather than only the coordinate identity.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1491, proof of Theorem 4.4, forward inclusion; DOI 10.1287/opre.1080.0646

import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem mixture_symmetric {N : ℕ} (hN : 0 < N)
    (lam : Fin (Nhat N) → ℝ) (h0 : ∀ j, 0 ≤ lam j)
    (h1 : ∑ j, lam j = 1) :
    (∀ i : Fin N, 2 / (N : ℝ) - (∑ j, lam j • qbar j) i =
      (∑ j, lam j • qbar j) (Fin.rev i)) ∧
    (∑ j, lam j • qbar j) ∈ symRestrictedSimplex N := by sorry

end RiskUncSets.Symmetric
