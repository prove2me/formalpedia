-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_unitary_circle_special_unitary
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.unitary_circle_special_unitary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:15:35.8264+00:00
-- url     : https://prove2.me/theorems/2040680d-3a5c-45c8-8ca9-6bcc9a4f9ee6
-- title:
--   Lemma 8
-- statement:
--   For an integer $n\ge1$, let $U(n)$ be the complex unitary group and let $SU(n)=\{U\in U(n):\det U=1\}$. Then
--
--   $$U(n)\cong_{\rm top} S^1\times SU(n),\qquad SU(n)\ \text{is simply connected}.$$
--
--   The circle is the unit circle in $\mathbb C$. The case $n=1$, in which $SU(1)$ is a point, is included; $n=0$ is excluded as in the source's first-coordinate construction. These are the topological ingredients for the rotation degree.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 7, Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 8, PDF pp.7–8; SU(1) is a point. -/
theorem unitary_circle_special_unitary {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (ComplexUnitary n ≃ₜ (UnitCircle × SpecialUnitary n)) ∧
      SimplyConnectedSpace (SpecialUnitary n) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
