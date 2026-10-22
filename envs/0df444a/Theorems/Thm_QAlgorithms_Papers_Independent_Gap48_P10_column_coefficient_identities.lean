-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_column_coefficient_identities
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.column_coefficient_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:23:51.932437+00:00
-- url     : https://prove2.me/theorems/09f1d6eb-1021-4058-8955-855d195341ad
-- title:
--   Lemma 6.1: column coefficient identities
-- statement:
--   Let $U\in SO(3)$ have entries in $\mathbb D[\sqrt2]$, and let $k\ge0$ be any common denominator exponent. Write
--
--   $$
--   U_{ij}=\frac{A_{ij}+B_{ij}\sqrt2}{(\sqrt2)^k},\qquad A_{ij},B_{ij}\in\mathbb Z.
--   $$
--   For every column pair $j,\ell$,
--
--   $$
--   \sum_i(A_{ij}B_{i\ell}+B_{ij}A_{i\ell})=0,\qquad
--   \sum_i(A_{ij}A_{i\ell}+2B_{ij}B_{i\ell})=2^k\delta_{j\ell}.
--   $$
--   In particular $\sum_iA_{ij}B_{ij}=0$ and $\sum_i(A_{ij}^2+2B_{ij}^2)=2^k$ for every column $j$. Here $\delta$ is the Kronecker delta.
--
--   These are identities of integer coefficients; minimality of the denominator exponent is unnecessary.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 6, Lemma 6.1: column coefficient identities

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 6.1, PDF p.6, equations (14)-(17). A and B package (a,c,e) and (b,d,f)
by column. No minimality of k is assumed. All conclusions are integer identities. -/
theorem column_coefficient_identities (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (k : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) ∧
    (∀ j, (∑ i, A i j * B i j) = 0 ∧
      (∑ i, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
