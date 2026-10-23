-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_hankel_four_extreme
-- name    : QAlgorithms.Papers.Independent.Information100.P19.hankel_four_extreme
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:46:57.080751+00:00
-- url     : https://prove2.me/theorems/f0586ef7-2f62-4d59-8e43-28f67c950703
-- title:
--   Proposition 3.8
-- statement:
--   Let $\Delta_{13}=p_1p_3-p_2^2=[31]-[22]$. Then
--   $$\Delta_{13}\in I_4^{\rm psd}\setminus I_4^{\rm all},\qquad
--   \mathbb R_{\ge0}\Delta_{13}\text{ is extremal in }I_4^{\rm psd}.$$
--   This distinguishes PSD positivity, failure on signed spectra, and extremality.
--
--   For a partition $\lambda$, the symbol $[\lambda]$ denotes a formal basis element evaluated as $\prod_j\operatorname{Tr}(X^{\lambda_j})$. Distinct formal coefficients are not identified by any fixed-dimensional trace identity.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 18, Proposition 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 3.8; arXiv:2609.29471v1, PDF pp.18, 19. -/
theorem hankel_four_extreme  :
    b31-b22 ∈ psdCone 4 ∧ b31-b22 ∉ allCone 4 ∧ Extreme (psdCone 4) (b31-b22) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
