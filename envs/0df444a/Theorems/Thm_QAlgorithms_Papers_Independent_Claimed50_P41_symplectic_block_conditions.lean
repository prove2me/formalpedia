-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_block_conditions
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_block_conditions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:59:22.351079+00:00
-- url     : https://prove2.me/theorems/4732432f-7920-40d2-bcdf-e77b52770fe8
-- title:
--   §IV (4.2): symplectic block conditions
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Let $S=\begin{pmatrix}A&B\\C&D\end{pmatrix}$ have real n by n blocks.
--
--   $$
--   S\beta S^T=\beta\iff AB^T,CD^T\text{ symmetric},\ AD^T-BC^T=I;\qquad S^T\beta S=\beta\iff A^TC,B^TD\text{ symmetric},\ A^TD-C^TB=I.
--   $$
--
--   The two block descriptions retain the original transpose placements and signs.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 11, §IV (4.2): symplectic block conditions

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.11, (4.2): both equivalent sets of block conditions. -/
theorem symplectic_block_conditions (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    (PreservesCanonicalForm (Matrix.fromBlocks A B C D) ↔
      (A * B.transpose).IsSymm ∧ (C * D.transpose).IsSymm ∧
        A * D.transpose - B * C.transpose = 1) ∧
    ((Matrix.fromBlocks A B C D).transpose * sigma n * Matrix.fromBlocks A B C D = sigma n ↔
      (A.transpose * C).IsSymm ∧ (B.transpose * D).IsSymm ∧
        A.transpose * D - C.transpose * B = 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
