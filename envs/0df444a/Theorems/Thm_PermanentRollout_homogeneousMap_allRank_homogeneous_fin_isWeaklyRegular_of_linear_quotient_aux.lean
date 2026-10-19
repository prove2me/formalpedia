-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
-- name    : PermanentRollout.homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/b9a90718-e51a-4710-8cad-cb32fb7f0fd6
-- title:
--   PermanentRollout.homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
    {ι : Type*} {e : ℕ}
    (ell : MvPolynomial ι ℂ)
    (hell : ell ≠ 0)
    (hellhom : ell.IsHomogeneous 1) :
    ∀ (n : ℕ) (f : Fin n → MvPolynomial ι ℂ),
      (∀ i, (f i).IsHomogeneous e) →
      RingTheory.Sequence.IsWeaklyRegular
        (MvPolynomial ι ℂ ⧸
          Ideal.span ({ell} : Set (MvPolynomial ι ℂ)))
        (List.ofFn fun i =>
          Ideal.Quotient.mk
            (Ideal.span ({ell} : Set (MvPolynomial ι ℂ))) (f i)) →
      RingTheory.Sequence.IsWeaklyRegular
        (MvPolynomial ι ℂ) (List.ofFn f) := by sorry
