-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_rotation_dimension_two
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.rotation_dimension_two
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:17:26.406341+00:00
-- url     : https://prove2.me/theorems/58088795-1bf6-43e3-8557-913178f12576
-- title:
--   Proposition 12
-- statement:
--   In dimension two, $\operatorname{Sp}(2,\mathbb R)=SL(2,\mathbb R)$. The determinant, conjugacy invariance and off-circle normalization conditions of Theorem 10 determine a unique continuous circle-valued map $\rho$. For $a=\operatorname{Tr}(A)/2$,
--
--   $$\rho(A)=\begin{cases}1,&a\ge1,\\-1,&a\le-1,\\\lambda,&|a|<1,\end{cases}$$
--
--   where in the last case $\lambda$ is the eigenvalue having a nonzero eigenvector $v-iw$ with $\Omega_0(v,w)>0$. Uniqueness is among maps on the symplectic group, not among arbitrary extensions outside it. This is the source's complete dimension-two rotation rule.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 11, Proposition 12

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 12, PDF p.11: uniqueness and all three trace regimes. -/
theorem rotation_dimension_two :
    RotationAxiomsTwo spectralRotation ∧
    (∀ r, RotationAxiomsTwo r → ∀ A, IsSymplectic A → r A = spectralRotation A) ∧
    (∀ A : GroupedRealMatrix 1, IsSymplectic A →
      (1 ≤ A.trace/2 → spectralRotation A = 1) ∧ (A.trace/2 ≤ -1 → spectralRotation A = -1) ∧
      (|A.trace/2| < 1 → ∀ z : ℂ, ∀ v w : Coord 1 → ℝ,
        (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0 →
        (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
          z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) →
        0 < omegaR v w → spectralRotation A = z)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
