-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotVar_of_le
-- name    : QECCertificates.LRAT.slotVar_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:16.37285+00:00
-- url     : https://prove2.me/theorems/a343dcac-3a6a-4fcc-a7af-0fa290ccaa5a
-- title:
--   LRAT: slot Var of le
-- statement:
--   `slotVar` takes a definite value on a valid slot.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L450-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L450-L452

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotVar_of_le {c k i j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) :
    slotVar c k i j = some (c + slotBase k i + (j - 1)) := by sorry
