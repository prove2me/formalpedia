-- Prove2me | Theorems.Thm_PermanentRollout_isSMulRegular_of_maximal_radical_and_regular_witness
-- name    : PermanentRollout.isSMulRegular_of_maximal_radical_and_regular_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/1dc126aa-82db-49f6-a9aa-67d928f56970
-- title:
--   PermanentRollout.isSMulRegular_of_maximal_radical_and_regular_witness
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

theorem PermanentRollout.isSMulRegular_of_maximal_radical_and_regular_witness
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (g ell : R) (m : Ideal R)
    (hm : m.IsMaximal)
    (hrad : (I ⊔ Ideal.span ({g} : Set R)).radical = m)
    (hellm : ell ∈ m)
    (hellregular : IsSMulRegular (R ⧸ I) ell) :
    IsSMulRegular (R ⧸ I) g := by sorry
