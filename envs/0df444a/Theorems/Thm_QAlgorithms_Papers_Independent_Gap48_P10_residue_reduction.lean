-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_residue_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.residue_reduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:29:00.154002+00:00
-- url     : https://prove2.me/theorems/f013a7ef-154f-45bc-81c8-4ffd11fd9cbf
-- title:
--   Lemma 7.8: residue reduction
-- statement:
--   Let $U$ be a unitary $2\times2$ matrix over $\mathbb D[\omega]$, and let $k\ge2$ be a common denominator exponent into $\mathbb Z[\omega]$. The residue $\rho_k(V)$ scales every entry by $(\sqrt2)^k$ before coefficient reduction modulo two. Assume $k$ also clears $HU$, as required for that residue to be defined. Suppose
--
--   $$
--   \rho_{k+1}(U)\sim_{\mathcal S}
--   \begin{pmatrix}0101&0101\\0101&0101\end{pmatrix},
--   $$
--
--   and $\rho_k(HU)$ is $\mathcal S$-equivalent to either $\begin{pmatrix}0011&0011\\0110&0110\end{pmatrix}$ or $\begin{pmatrix}0011&0011\\1001&1001\end{pmatrix}$. Then
--
--   $$
--   \rho_k(U)\sim_{\mathcal S}
--   \begin{pmatrix}1000&0111\\0111&1000\end{pmatrix}.
--   $$
--   Equivalence is right multiplication by the residues of $\mathcal S=\langle S,X,\omega I\rangle$, including the independent second-column shift. No least-exponent assumption is imposed.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 9, Lemma 7.8: residue reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 7.8, PDF p.9. k is a denominator exponent, not necessarily the least.
The exponent for HU is explicitly valid so totalized residues are never used
outside their domain; the first residue is at k+1 and the other two at k. -/
theorem residue_reduction (U : Mat) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (hring : ∀ i j, InDomega (U i j)) (k : ℕ) (hk : 2 ≤ k)
    (hdenom : complexDenominator U k)
    (hHdenom : complexDenominator (QAlgorithms.hadamard * U) k)
    (hfirst : residueEquivalent (matrixResidue U (k + 1)) (residueMatrix 5 5 5 5))
    (hsecond : residueEquivalent (matrixResidue (QAlgorithms.hadamard * U) k) (residueMatrix 3 3 6 6) ∨
      residueEquivalent (matrixResidue (QAlgorithms.hadamard * U) k) (residueMatrix 3 3 9 9)) :
    residueEquivalent (matrixResidue U k) (residueMatrix 8 7 7 8) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
