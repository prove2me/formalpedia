-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_so3_parity_alternatives
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.so3_parity_alternatives
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:25:44.991487+00:00
-- url     : https://prove2.me/theorems/1cf38d46-3783-412e-b915-8f96b6b9aac4
-- title:
--   Lemma 6.3: SO(3) parity alternatives
-- statement:
--   Let $U\in SO(3)$ have entries in $\mathbb D[\sqrt2]$, and let $k$ be its least natural common denominator exponent over $\mathbb Z[\sqrt2]$. If $k=0$, then $U$ is the Bloch image of an operator in $\mathcal C$. If $k>0$, then
--
--   $$
--   p_k(U)\sim P_T\quad\text{or}\quad p_k(U)\sim P_H\quad\text{or}\quad p_k(U)\sim P_S,
--   $$
--   where $\sim$ permits column permutations only, and $P_T,P_H,P_S$ are respectively the binary matrices with rows $(110,110,000)$, $(000,110,110)$ and $(110,000,110)$. The parity $p_k$ reduces constant coefficients modulo two after multiplication by $(\sqrt2)^k$.
--
--   This exhausts the zero- and positive-exponent cases for all such rotations.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 6, Lemma 6.3: SO(3) parity alternatives

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 6.3, PDF p.6. The zero-exponent case and all three positive-exponent
patterns are retained. Column permutation is the only parity equivalence. -/
theorem so3_parity_alternatives (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) :
    (realLde U = 0 → ∃ C : Clifford, operatorBloch C.val = U) ∧
    (0 < realLde U → ∃ r : Fin 3,
      parityEquivalent (matrixParity U (realLde U)) (parityPattern r)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
