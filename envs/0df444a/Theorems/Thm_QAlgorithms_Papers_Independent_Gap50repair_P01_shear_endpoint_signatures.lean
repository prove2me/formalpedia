-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_shear_endpoint_signatures
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.shear_endpoint_signatures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:26:54.22152+00:00
-- url     : https://prove2.me/theorems/ad5a2042-460a-4dee-b96c-d3e1822c0b96
-- title:
--   Proposition 54
-- statement:
--   Let $B:[0,1]\to\operatorname{Mat}(n,\mathbb R)$ be continuous with each $B(t)$ symmetric. For the upper symplectic shear $\psi(t)=\left(\begin{smallmatrix}I&B(t)\\0&I\end{smallmatrix}\right)$,
--
--   $$\mu_{\rm RS}(\psi)=\tfrac12\operatorname{Sign}B(0)-\tfrac12\operatorname{Sign}B(1).$$
--
--   Signatures count positive minus negative inertia, including zero eigenvalues. No regular-crossing or nonsingularity hypothesis is imposed. This fixes the shear sign convention for arbitrary continuous symmetric paths.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 51, Proposition 54

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 54, PDF pp.51–52: only continuity and symmetry, no regularity assumption. -/
theorem shear_endpoint_signatures {n : ℕ} (B : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hc : ContinuousOn B (Set.Icc (0 : ℝ) 1))
    (hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, (B t).transpose = B t) :
    robbinSalamon (fun t => shear (B t)) =
      (matrixSignature (B 0) : ℚ)/2 - (matrixSignature (B 1) : ℚ)/2 := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
