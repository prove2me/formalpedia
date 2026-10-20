-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideProduct_pderiv
-- name    : PermanentFormulaLowerBound.matchingPermutationOutsideProduct_pderiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/6542ad65-3673-421d-8fe6-47189cc5f1bb
-- title:
--   PermanentFormulaLowerBound.matchingPermutationOutsideProduct_pderiv
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

theorem PermanentFormulaLowerBound.matchingPermutationOutsideProduct_pderiv
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (z : matchingOutside d) :
    MvPolynomial.pderiv z (matchingPermutationOutsideProduct d σ) =
      if σ z.1.1 = z.1.2 then
        ∏ i : {i : Fin n // i ≠ z.1.1},
          matchingPermutationOutsideFactor d σ i.1
      else 0 := by sorry
