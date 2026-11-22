-- Prove2me | Theorems.Thm_QECCertificates_LRAT_rowFill_of_notMem
-- name    : QECCertificates.LRAT.rowFill_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:16.397141+00:00
-- url     : https://prove2.me/theorems/76731bc6-182e-470b-a194-22f736321dc4
-- title:
--   LRAT: row Fill of not Mem
-- statement:
--   Outside the block the assignment is kept as it is.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L713-L717
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L713-L717

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.rowFill_of_notMem {τ : Assign} {c k i cnt t : Nat}
    (h : ¬ (c + slotBase k i ≤ t ∧ t < c + slotBase k i + min i (k + 1))) :
    rowFill τ c k i cnt t = τ t := by sorry
