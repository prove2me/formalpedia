-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_pre_iwasawa_explicit_unique
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.pre_iwasawa_explicit_unique
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:02:38.545331+00:00
-- url     : https://prove2.me/theorems/13198996-4af0-4b67-a985-23f6723cca8d
-- title:
--   §IV (4.21): explicit unique pre-Iwasawa factors
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For $S=\begin{pmatrix}A&B\\C&D\end{pmatrix}\in\mathrm{Sp}$ put $R=(AA^T+BB^T)^{1/2}$, $C_0=(CA^T+DB^T)R^{-1}$, $X=R^{-1}A$ and $Y=R^{-1}B$.
--
--   $$
--   S=L(C_0R^{-1})\operatorname{diag}(R,R^{-1})K(X-iY).
--   $$
--
--   The root is symmetric positive definite and nonsingular, C0 R inverse is symmetric, and X-iY is unitary. All constrained factors are unique. These quantities are constructed from S rather than supplied as extra hypotheses.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 16, §IV (4.21): explicit unique pre-Iwasawa factors

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.16–17, (4.21): all constructed factors are valid and unique.
A0 and C0 are definitions of the input blocks, never extra hypotheses. -/
theorem pre_iwasawa_explicit_unique (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) :
    let R := preA A B
    let Czero := preC A B C D
    let X := R⁻¹ * A
    let Y := R⁻¹ * B
    (A * A.transpose + B * B.transpose).PosDef ∧ R.PosDef ∧
    R * R = A * A.transpose + B * B.transpose ∧ IsUnit R.det ∧
    (Czero * R⁻¹).IsSymm ∧ IsPassive (passiveMatrix X Y) ∧
    unitaryParameter X Y = complexify R⁻¹ * unitaryParameter A B ∧
    Matrix.fromBlocks A B C D = lensMatrix (Czero * R⁻¹) * glMatrix R * passiveMatrix X Y ∧
    (∃! f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Matrix (Phase n) (Phase n) ℝ,
      f.1.IsSymm ∧ f.2.1.PosDef ∧ IsPassive f.2.2 ∧
        Matrix.fromBlocks A B C D = lensMatrix f.1 * glMatrix f.2.1 * f.2.2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
