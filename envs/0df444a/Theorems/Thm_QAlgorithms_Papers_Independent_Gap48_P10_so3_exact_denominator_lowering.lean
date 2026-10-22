-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_so3_exact_denominator_lowering
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.so3_exact_denominator_lowering
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:26:20.975577+00:00
-- url     : https://prove2.me/theorems/89732163-873e-4469-8a45-9e181be51437
-- title:
--   Lemma 6.4: exact denominator lowering
-- statement:
--   Let $U\in SO(3)$ have entries in $\mathbb D[\sqrt2]$ and least natural common denominator exponent $k>0$. Then
--
--   $$
--   \exists N\in\{T,HT,SHT\},\qquad
--   \operatorname{lde}(\widehat N^{-1}U)=k-1.
--   $$
--   Here exponents clear all real entries into $\mathbb Z[\sqrt2]$, the Bloch map uses ordered $X,Y,Z$ coordinates, and inverse equals transpose for its orthogonal matrices.
--
--   This is an exact decrease of the least exponent, not merely an upper bound.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 6, Lemma 6.4: exact denominator lowering

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 6.4, PDF pp.6-7. The new least exponent is exactly k-1, with k>0.
Transpose is inverse for the source's real orthogonal Bloch matrices. -/
theorem so3_exact_denominator_lowering (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (hk : 0 < realLde U) :
    ∃ r : Fin 3,
      realLde ((operatorBloch (leftSyllable r)).transpose * U) = realLde U - 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
