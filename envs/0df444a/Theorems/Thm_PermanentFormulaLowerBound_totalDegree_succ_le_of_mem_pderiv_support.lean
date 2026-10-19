-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_totalDegree_succ_le_of_mem_pderiv_support
-- name    : PermanentFormulaLowerBound.totalDegree_succ_le_of_mem_pderiv_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/9f706caa-e5bf-42f1-a37d-17faba2cbd0c
-- title:
--   PermanentFormulaLowerBound.totalDegree_succ_le_of_mem_pderiv_support
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

theorem PermanentFormulaLowerBound.totalDegree_succ_le_of_mem_pderiv_support [CommSemiring F]
    (p : MvPolynomial ι F) (i : ι) {m : ι →₀ ℕ}
    (hm : m ∈ (MvPolynomial.pderiv i p).support) :
    Multiset.card (Finsupp.toMultiset m) + 1 ≤ p.totalDegree := by sorry
