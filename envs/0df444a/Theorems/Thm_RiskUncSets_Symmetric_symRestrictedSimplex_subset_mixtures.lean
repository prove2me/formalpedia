-- Prove2me | Theorems.Thm_RiskUncSets_Symmetric_symRestrictedSimplex_subset_mixtures
-- name    : RiskUncSets.Symmetric.symRestrictedSimplex_subset_mixtures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:57.129389+00:00
-- url     : https://prove2.me/theorems/08fbaf19-a775-493b-b43f-05b55bab4ee8
-- title:
--   Proof of Theorem 4.4: every symmetric restricted weight is a generator mixture
-- statement:
--   Let $N\ge1$ and take $q$ in the symmetric restricted simplex $\widehat\Delta^N_{\mathrm{sym}}$. There are nonnegative coefficients $\lambda_1,\ldots,\lambda_{\widehat N}$ summing to one such that
--
--   $$
--   q=\sum_{j=1}^{\widehat N}\lambda_j\bar q^{j}.
--   $$
--
--   This gives the reverse inclusion and establishes that the displayed generator family spans the entire symmetric subclass.
--
--   **Formalization Note** The source constructs the coefficients from the final coordinates of $q$; the Lean statement records the resulting existence claim. The source's printed intermediate sum on p. 1492 has an indexing slip, while its claimed conclusion $\sum_j\lambda_j=1$ is retained.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1492, proof of Theorem 4.4, reverse inclusion; DOI 10.1287/opre.1080.0646

import Definitions.Def_RiskUncSets_Symmetric_Setting

namespace RiskUncSets.Symmetric

theorem symRestrictedSimplex_subset_mixtures {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) (hq : q ∈ symRestrictedSimplex N) :
    ∃ lam : Fin (Nhat N) → ℝ,
      (∀ j, 0 ≤ lam j) ∧
      ∑ j, lam j = 1 ∧
      q = ∑ j, lam j • qbar j := by sorry

end RiskUncSets.Symmetric
