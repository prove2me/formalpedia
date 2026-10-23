-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_polar_projection_degree
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.polar_projection_degree
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:23:52.01453+00:00
-- url     : https://prove2.me/theorems/936b14db-53f8-4458-90e3-e989d168cde0
-- title:
--   Corollary 39
-- statement:
--   Let $n\ge1$, let $\gamma$ be admissible, and let $e$ be any admissible extension. For a symplectic matrix $A$, let $P(A)$ be the unique symmetric positive definite square root of $A^\mathsf TA$ and put $U(A)=A P(A)^{-1}$. Then
--
--   $$\mu_{\rm CZ}(\gamma)=\deg\bigl((\det_\mathbb C\circ U\circ e)^2\bigr).$$
--
--   Thus the polar projection is a computed function of $A$, rather than an arbitrary map supplied with a compatibility assumption. The formula connects the classical index with the polar definition used elsewhere.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 42, Corollary 39

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Corollary 39, PDF p.42: U(A)=A P(A)^-1 is computed, not an assumed projection. -/
theorem polar_projection_degree {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1) (he : IsExtension p e) :
    conleyZehnder p 1 = winding (fun t => complexActionDet (polarU (e t))^2) 2 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
