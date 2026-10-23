-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_product_translated_catenation
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.product_translated_catenation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:22:27.646045+00:00
-- url     : https://prove2.me/theorems/33236d9a-8ae9-4ae1-850c-b4d97af325d5
-- title:
--   Lemma 36
-- statement:
--   Let $T>0$ and let $\phi,\psi:[0,T]\to\operatorname{Sp}(2n,\mathbb R)$ be continuous paths with $\phi(0)=\psi(0)=I$. Their pointwise product $t\mapsto\psi(t)\phi(t)$ is homotopic with fixed endpoints to
--
--   $$(\psi\diamond\phi)(t)=\begin{cases}\phi(2t),&t\le T/2,\\\psi(2t-T)\phi(T),&t\ge T/2.\end{cases}$$
--
--   Both branches agree at $t=T/2$. No final nondegeneracy condition is required. This identifies pointwise multiplication with translated catenation for index calculations.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 38, Lemma 36

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 36, PDF p.38, with the common endpoints fixed. -/
theorem product_translated_catenation {n : ℕ} (T : ℝ) (hT : 0 < T)
    (phi psi : ℝ → GroupedRealMatrix n) (hp : IsPath phi T) (hq : IsPath psi T)
    (hp0 : phi 0 = 1) (hq0 : psi 0 = 1) :
    FixedHomotopic (fun t => psi t*phi t) (translatedCatenate phi psi T) T := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
