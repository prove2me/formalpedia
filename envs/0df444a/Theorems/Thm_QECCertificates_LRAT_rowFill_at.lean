-- Prove2me | Theorems.Thm_QECCertificates_LRAT_rowFill_at
-- name    : QECCertificates.LRAT.rowFill_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:25.146872+00:00
-- url     : https://prove2.me/theorems/822ae21e-c9a6-4c0d-b433-e4bcb536ba4e
-- title:
--   LRAT: row Fill at
-- statement:
--   The value of the `j`-th slot inside the block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L705-L710
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L705-L710

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.rowFill_at {τ : Assign} {c k i cnt j : Nat} (hj : j < min i (k + 1)) :
    rowFill τ c k i cnt (c + slotBase k i + j) = decide (j + 1 ≤ cnt) := by sorry
