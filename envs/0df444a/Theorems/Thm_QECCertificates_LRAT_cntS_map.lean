-- Prove2me | Theorems.Thm_QECCertificates_LRAT_cntS_map
-- name    : QECCertificates.LRAT.cntS_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:56.202968+00:00
-- url     : https://prove2.me/theorems/f479682a-8ee6-46de-9a3f-2aa9e3f76362
-- title:
--   LRAT: cnt S map
-- statement:
--   The invariance of the support size under a map, exchanging a list of variable numbers
--   for an assignment indexed by column.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L433-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L433-L435

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.cntS_map (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    cntS σ (l.map f) = cntS (fun t => σ (f t)) l := by sorry
