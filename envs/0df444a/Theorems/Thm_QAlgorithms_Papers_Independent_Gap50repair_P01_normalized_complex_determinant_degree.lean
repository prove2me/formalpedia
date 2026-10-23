-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_normalized_complex_determinant_degree
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.normalized_complex_determinant_degree
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:24:14.284715+00:00
-- url     : https://prove2.me/theorems/f48c27e0-2bc0-444b-bfc7-ead357e247c8
-- title:
--   Corollary 40
-- statement:
--   For $A\in\operatorname{Sp}(2n,\mathbb R)$ put $C_A=\tfrac12(A-J_0AJ_0)$. This real matrix is invertible, and its complex determinant is nonzero. Define $\widehat\rho(A)=\det_\mathbb C C_A/|\det_\mathbb C C_A|$. For $n\ge1$, any admissible path $\gamma$ and any admissible extension $e$ satisfy
--
--   $$\mu_{\rm CZ}(\gamma)=\deg(\widehat\rho^{\,2}\circ e).$$
--
--   The denominator is an absolute value, as printed in (45); invertibility is established from symplecticity and is not an extra input hypothesis. This is the normalized complex-linear-part formula.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 42, Corollary 40

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Corollary 40, PDF p.42; absolute-value denominator visually verified.
Invertibility is a conclusion from symplecticity. -/
theorem normalized_complex_determinant_degree {n : ℕ} (hn : 1 ≤ n)
    (p e : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1) (he : IsExtension p e) :
    (∀ A : GroupedRealMatrix n, IsSymplectic A →
      (complexLinearPart A).det ≠ 0 ∧ complexActionDet (complexLinearPart A) ≠ 0) ∧
    conleyZehnder p 1 = winding (fun t => normalizedDet (e t)^2) 2 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
