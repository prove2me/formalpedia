-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_alternating_contractions
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.alternating_contractions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:47:40.975835+00:00
-- url     : https://prove2.me/theorems/78fde86f-e358-4cf5-a0dd-10e6c3fd4ff8
-- title:
--   Proposition A.3.
-- statement:
--   Let $d\ge1$. Vectorization is unnormalized: $|A\rangle=\sum_{i,j}A_{ij}|i,j\rangle$. In Appendix A only, $\langle A|=|A\rangle^T$ is bilinear, without complex conjugation. The formal tensor contractions are independent sums over the internal path indices, in their displayed order. Put $S=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $|\Psi^-\rangle=|S\rangle/\sqrt2$.
--
--   For $k\ge0$ and matrices $A_1,\ldots,A_{k+1},B_1,\ldots,B_{k+1}$, the three alternating network contractions are respectively
--   $$A_1B_1\cdots A_kB_k,\qquad|A_1B_1\cdots A_kB_kA_{k+1}\rangle,\qquad\operatorname{Tr}(A_1B_1\cdots A_{k+1}B_{k+1}).$$
--   The contractions have the exact order of (A.10)–(A.12). At $k=0$, they give identity, $|A_1\rangle$, and $\operatorname{Tr}(A_1B_1)$.
--
--   This fixes the contraction and sign conventions used in the singlet-diagram analysis.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 46, Proposition A.3.

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

/-- PDF p.46, Proposition A.3: all three tensor-contraction types, including
k=0. Network index sums preserve the order of the source tensor contractions. -/
theorem alternating_contractions (d k : ℕ) (hd : 1 ≤ d)
    (A B : Fin (k+1) → Op (Fin d)) :
    networkChain (2*k) (alternatingFactors k 0 A B) = alternatingMatrixProduct k A B ∧
    bilinearVectorize (networkChain (2*k+1) (alternatingFactors k 1 A B)) =
      bilinearVectorize (alternatingMatrixProduct k A B * A ⟨k,by omega⟩) ∧
    (networkChain (2*k+2) (alternatingFactors k 2 A B)).trace =
      (alternatingMatrixProduct k A B * A ⟨k,by omega⟩ * B ⟨k,by omega⟩).trace := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
