-- Prove2me | Theorems.Thm_QECCertificates_LRAT_vecOf_apply_ne_zero
-- name    : QECCertificates.LRAT.vecOf_apply_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:32.539836+00:00
-- url     : https://prove2.me/theorems/3073729a-dff0-4cc3-b98d-3187462f3325
-- title:
--   LRAT: vec Of apply ne zero
-- statement:
--   Nonzeroness for `vecOf`: entry `i` is nonzero if and only if `σ` is true there.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L41-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L41-L44

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.vecOf_apply_ne_zero {σ : Assign} {n : ℕ} {i : Fin n} :
    vecOf σ n i ≠ 0 ↔ σ i.val = true := by sorry
