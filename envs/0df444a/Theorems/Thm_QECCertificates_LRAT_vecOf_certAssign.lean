-- Prove2me | Theorems.Thm_QECCertificates_LRAT_vecOf_certAssign
-- name    : QECCertificates.LRAT.vecOf_certAssign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:03.784749+00:00
-- url     : https://prove2.me/theorems/155ca3ed-d120-4c22-a14c-44772b0dd716
-- title:
--   LRAT: vec Of cert Assign
-- statement:
--   The first `n` bits of the assignment read back as the kernel vector itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L197-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L197-L200

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.vecOf_certAssign {n : ℕ} (E w : Vec n) : vecOf (certAssign n E w) n = E := by sorry
