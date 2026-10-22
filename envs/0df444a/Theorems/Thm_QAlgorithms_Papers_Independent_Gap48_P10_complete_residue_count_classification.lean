-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_complete_residue_count_classification
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.complete_residue_count_classification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:29:32.575643+00:00
-- url     : https://prove2.me/theorems/049a7a6b-bc4c-410f-9454-02cb4a9d2f2b
-- title:
--   Theorem 7.10: complete Figure-2 residue/count classification
-- statement:
--   Let $M$ have the modified Matsumoto–Amano syntax
--
--   $$
--   (T\mid\varepsilon)(HT\mid SHT)^*(\varepsilon\mid H\mid SH)A,\qquad A\in\mathcal S.
--   $$
--   Let $U$ be its exact matrix, $t$ the number of displayed $T$ letters, $h$ the number of displayed $H$ letters, and $k$ the least exponent clearing the entries of $U$ into $\mathbb Z[\omega]$. The atomic terminal $A$ contributes zero to both counts. Exactly one of the 26 reduced unstarred vertices of Figure 2 has pattern $\mathcal S$-equivalent to $\rho_k(U)$, and every count equality and exponent threshold on that vertex holds.
--
--   $$
--   \exists!\,\text{residue-match vertex }v,\qquad
--   2k-t=\Delta_T(v),\quad 2k-h=\Delta_H(v),
--   $$
--   with the vertex's exact exponent $k=0$ or $k=1$, or its lower threshold $k\ge2$, as applicable. The accompanying Lean table transcribes all 26 patterns and their labels, excluding both single-star duplicates and both double-star unreduced vertices. Uniqueness concerns the residue match independently of the count labels.
--
--   This retains the full finite classification rather than just its count-bound corollary.
--
--   The retained vertex table is:
--
--   | Residue pattern | $\Delta_T=2k-t$ | $\Delta_H=2k-h$ | Exponent condition |
--   |---|---:|---:|---|
--   | $\begin{pmatrix}0001&0000\\0000&0001\end{pmatrix}$ | 0 | 0 | $k=0$ |
--   | $\begin{pmatrix}0001&0000\\0000&0010\end{pmatrix}$ | -1 | 0 | $k=0$ |
--   | $\begin{pmatrix}0001&0001\\0001&0001\end{pmatrix}$ | 2 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0001\\0100&0100\end{pmatrix}$ | 2 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0010\\0001&0010\end{pmatrix}$ | 1 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0010\\0100&1000\end{pmatrix}$ | 1 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0001\\0010&0010\end{pmatrix}$ | 1 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0001\\1000&1000\end{pmatrix}$ | 1 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0010\\0010&0100\end{pmatrix}$ | 0 | 1 | $k=1$ |
--   | $\begin{pmatrix}0001&0010\\1000&0001\end{pmatrix}$ | 0 | 1 | $k=1$ |
--   | $\begin{pmatrix}0011&0011\\0011&0011\end{pmatrix}$ | 3 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0011\\1100&1100\end{pmatrix}$ | 3 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0110\\0011&0110\end{pmatrix}$ | 2 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0110\\1100&1001\end{pmatrix}$ | 2 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0011\\0110&0110\end{pmatrix}$ | 2 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0011\\1001&1001\end{pmatrix}$ | 2 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0110\\0110&1100\end{pmatrix}$ | 1 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}0011&0110\\1001&0011\end{pmatrix}$ | 1 | 2 | $k\ge2$ |
--   | $\begin{pmatrix}1000&0111\\0111&1000\end{pmatrix}$ | 2 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&0111\\1101&0010\end{pmatrix}$ | 2 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&1110\\0111&0001\end{pmatrix}$ | 1 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&1110\\1101&0100\end{pmatrix}$ | 1 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&0111\\1110&0001\end{pmatrix}$ | 1 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&0111\\1011&0100\end{pmatrix}$ | 1 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&1110\\1110&0010\end{pmatrix}$ | 0 | 1 | $k\ge2$ |
--   | $\begin{pmatrix}1000&1110\\1011&1000\end{pmatrix}$ | 0 | 1 | $k\ge2$ |
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 9, Theorem 7.10: complete Figure-2 residue/count classification

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Theorem 7.10, PDF pp.9-10: the COMPLETE 26-vertex classification.
Uniqueness applies to the residue match itself, independently of the count label.
All count equalities, exact base exponents, and lower thresholds are included. -/
theorem complete_residue_count_classification (M : ModifiedForm) :
    let U := modifiedValue M
    let k := complexLde U
    ∃ i : Fin 26,
      residueEquivalent (matrixResidue U k) (figureVertices i).pattern ∧
      (∀ j : Fin 26, residueEquivalent (matrixResidue U k) (figureVertices j).pattern → j = i) ∧
      VertexCounts (figureVertices i) (modifiedTCount M) (modifiedHCount M) k := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
