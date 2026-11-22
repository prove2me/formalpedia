-- Prove2me | Theorems.Thm_QECCertificates_LRAT_vecOf_and
-- name    : QECCertificates.LRAT.vecOf_and
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:18.644078+00:00
-- url     : https://prove2.me/theorems/ac5c5b13-1ec2-4597-a50a-c29573a90a18
-- title:
--   LRAT: vec Of and
-- statement:
--   The reading of bitwise conjunction: `vecOf` sends `&&` to multiplication in `ZMod 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L214-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L214-L218

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.vecOf_and {n : ℕ} (a b : Assign) :
    vecOf (fun t => a t && b t) n = fun i => vecOf a n i * vecOf b n i := by sorry
