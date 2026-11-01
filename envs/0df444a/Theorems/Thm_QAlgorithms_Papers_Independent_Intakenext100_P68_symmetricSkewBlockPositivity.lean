-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_symmetricSkewBlockPositivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.symmetricSkewBlockPositivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:35:58.09593+00:00
-- url     : https://prove2.me/theorems/35a38681-6a8e-43d1-af26-4203753f31b0
-- title:
--   Real symmetric/skew block positivity equals positivity of A+iC
-- statement:
--   Let $A,C\in\mathbb R^{n\times n}$ satisfy $A^T=A$ and $C^T=-C$, and put $M=\begin{pmatrix}A&C\\C^T&A\end{pmatrix}$. No positivity assumption on $A$ is imposed. Then
--
--   $$
--   M\succeq0\quad\Longleftrightarrow\quad A+iC\succeq0.
--   $$
--
--   The right-hand side is complex Hermitian positivity. This finite matrix lemma converts the equal-diagonal real block form into one complex Hermitian matrix.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 4, Appendix Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Topology ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsSeparable IsBarycenter productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

/-- PDF p.4, Appendix Lemma 2: A symmetric and C skew-symmetric, without
PSD assumption on A. Both directions and the PLUS sign in A+iC are retained. -/
theorem symmetricSkewBlockPositivity {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) (hC : C.transpose = -C) :
    (Matrix.fromBlocks A C C.transpose A).PosSemidef ↔
      (complexify A + Complex.I • complexify C).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
