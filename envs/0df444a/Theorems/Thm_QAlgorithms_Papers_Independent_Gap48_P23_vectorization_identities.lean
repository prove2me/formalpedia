-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_vectorization_identities
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.vectorization_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:47:04.950335+00:00
-- url     : https://prove2.me/theorems/ff790483-40e8-4979-8d4f-f7616e378f8e
-- title:
--   Proposition A.2.
-- statement:
--   Let $d\ge1$. Vectorization is unnormalized: $|A\rangle=\sum_{i,j}A_{ij}|i,j\rangle$. In Appendix A only, $\langle A|=|A\rangle^T$ is bilinear, without complex conjugation. The formal tensor contractions are independent sums over the internal path indices, in their displayed order. Put $S=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $|\Psi^-\rangle=|S\rangle/\sqrt2$.
--
--   For any $d\times d$ matrices $A,B$, the four vectorization identities are
--   $$\langle B|A\rangle=\operatorname{Tr}(AB^T),\quad\mathrm{SWAP}|A\rangle=|A^T\rangle,\quad(B\otimes I)|A\rangle=|BA\rangle,\quad(I\otimes\langle B|)(|A\rangle\otimes I)=AB.$$
--   The bilinear convention is essential for the first and fourth formulas.
--
--   This fixes the contraction and sign conventions used in the singlet-diagram analysis.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 45, Proposition A.2.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.45-46, Proposition A.2: all four identities, with the bilinear bra. -/
theorem vectorization_identities (d : ℕ) (hd : 1 ≤ d) (A B : Op (Fin d)) :
    vectorizedBra B (bilinearVectorize A) = (A * B.transpose).trace ∧
    (vectorSwap d).mulVec (bilinearVectorize A) = bilinearVectorize A.transpose ∧
    (Matrix.kronecker B (1 : Op (Fin d))).mulVec (bilinearVectorize A) = bilinearVectorize (B*A) ∧
    singleContraction A B = A*B := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
