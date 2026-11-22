-- Prove2me | Theorems.Thm_QECCertificates_LRAT_zmod2_eq_one_of_ne_zero
-- name    : QECCertificates.LRAT.zmod2_eq_one_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:31.658693+00:00
-- url     : https://prove2.me/theorems/83eeba42-0ac1-42d2-8a95-1c646873bbac
-- title:
--   LRAT: zmod2 eq one of ne zero
-- statement:
--   In `ZMod 2` everything nonzero is one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L156-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L156-L161

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by sorry
