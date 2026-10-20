-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_totalDegree_pderiv_lt_of_ne_zero
-- name    : PermanentFormulaLowerBound.totalDegree_pderiv_lt_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/d5c85761-84f3-4249-bc06-a002407e5cdd
-- title:
--   PermanentFormulaLowerBound.totalDegree_pderiv_lt_of_ne_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}

theorem PermanentFormulaLowerBound.totalDegree_pderiv_lt_of_ne_zero [CommSemiring F]
    (p : MvPolynomial ι F) (i : ι)
    (hp : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by sorry
