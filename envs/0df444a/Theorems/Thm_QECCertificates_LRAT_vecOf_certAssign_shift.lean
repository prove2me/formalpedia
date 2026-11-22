-- Prove2me | Theorems.Thm_QECCertificates_LRAT_vecOf_certAssign_shift
-- name    : QECCertificates.LRAT.vecOf_certAssign_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:18.214981+00:00
-- url     : https://prove2.me/theorems/db673072-8322-4a29-b57d-e727da71b695
-- title:
--   LRAT: vec Of cert Assign shift
-- statement:
--   The next `n` bits of the assignment read back as the pairing witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L203-L211
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L203-L211

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.vecOf_certAssign_shift {n : ℕ} (E w : Vec n) :
    vecOf (fun t => certAssign n E w (n + t)) n = w := by sorry
