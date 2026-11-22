-- Prove2me | Theorems.Thm_QECCertificates_LRAT_rowFill_prev
-- name    : QECCertificates.LRAT.rowFill_prev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:59.104997+00:00
-- url     : https://prove2.me/theorems/a53fce07-b29d-4f96-a347-f87d63a35b66
-- title:
--   LRAT: row Fill prev
-- statement:
--   Filling row `i` leaves the block of row `i-1` untouched (the two blocks meet end to end
--   without overlapping).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L721-L727
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L721-L727

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.rowFill_prev {τ : Assign} {c k i cnt j : Nat} (hi : 1 ≤ i)
    (hj : j < min (i - 1) (k + 1)) :
    rowFill τ c k i cnt (c + slotBase k (i - 1) + j) = τ (c + slotBase k (i - 1) + j) := by sorry
