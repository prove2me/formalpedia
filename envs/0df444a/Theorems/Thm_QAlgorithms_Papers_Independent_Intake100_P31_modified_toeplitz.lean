-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_modified_toeplitz
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.modified_toeplitz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:46:01.626994+00:00
-- url     : https://prove2.me/theorems/65ea512e-b1e7-43bb-9bac-5435a612dd9f
-- title:
--   §II.C: modified Toeplitz families are both universal and dual universal
-- statement:
--   Let $a\ge0$ and $b\ge1$. Choose a uniformly random binary $b\times a$ Toeplitz matrix $T_r$ and form $M_r=(T_r,I_b)$ and $N_r=(I_a,T_r^{\mathsf T})$. Both induced hash families are universal with parameter one, both maps are surjective for every seed, their kernels are dual, and
--
--   $$M_rN_r^{\mathsf T}=0\quad\text{for every }r.$$
--
--   The formal seed has $a+b$ independent bits, one of which is unused when both dimensions are positive. This gives the usual uniform Toeplitz distribution with equal repeated multiplicities, and also handles $a=0$.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 6, §II.C: modified Toeplitz families are both universal and dual universal

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.3,6: both modified Toeplitz families are universal, surjective, and dual.
A redundant uniform seed bit preserves the distribution of all Toeplitz matrices. -/
theorem modified_toeplitz (a b : ℕ) (hb : 0 < b) :
    HashUniversal (fun r => Matrix.toLin' (modifiedM a b r)) 1 ∧
    HashUniversal (fun r => Matrix.toLin' (modifiedN a b r)) 1 ∧
    (∀ r, Function.Surjective (Matrix.toLin' (modifiedM a b r))) ∧
    (∀ r, Function.Surjective (Matrix.toLin' (modifiedN a b r))) ∧
    (∀ r, modifiedM a b r * (modifiedN a b r).transpose = 0) ∧
    (∀ r, LinearMap.ker (Matrix.toLin' (modifiedM a b r)) =
      binDual (LinearMap.ker (Matrix.toLin' (modifiedN a b r)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
