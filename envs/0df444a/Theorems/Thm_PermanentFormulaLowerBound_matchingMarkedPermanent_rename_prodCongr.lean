-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_rename_prodCongr
-- name    : PermanentFormulaLowerBound.matchingMarkedPermanent_rename_prodCongr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/539bd36a-615b-434b-9de8-a0f053d43ac9
-- title:
--   PermanentFormulaLowerBound.matchingMarkedPermanent_rename_prodCongr
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

theorem PermanentFormulaLowerBound.matchingMarkedPermanent_rename_prodCongr
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (r c : Equiv.Perm (Fin n))
    (he : ∀ y : Y, Equiv.prodCongr r c (d₀ y) = d y) :
    MvPolynomial.renameEquiv ℂ
        (Equiv.sumCongr (Equiv.refl Y)
          (matchingOutsideRelabelEquiv d₀ d
            (Equiv.prodCongr r c) he))
        (matchingMarkedPermanent d₀) =
      matchingMarkedPermanent d := by sorry
