-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotVar_eq_none
-- name    : QECCertificates.LRAT.slotVar_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:04.746261+00:00
-- url     : https://prove2.me/theorems/baf64865-a07e-4564-80b5-b38a8b2d327c
-- title:
--   LRAT: slot Var eq none
-- statement:
--   `slotVar` takes `none` on an invalid slot.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L455-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L455-L457

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotVar_eq_none {c k i j : Nat} (h : ¬ (1 ≤ j ∧ j ≤ min i (k + 1))) :
    slotVar c k i j = none := by sorry
