-- Prove2me | Theorems.Thm_QECCertificates_LRAT_prodFill_of_lt
-- name    : QECCertificates.LRAT.prodFill_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:06.041238+00:00
-- url     : https://prove2.me/theorems/f0d898c2-9b0c-4c61-8ad9-20d40277fe7a
-- title:
--   LRAT: prod Fill of lt
-- statement:
--   The product block does not touch the input variables (`c` lies above them).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L403-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L403-L406

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.prodFill_of_lt {σ : Assign} {c n t : Nat} (h : t < c) :
    prodFill σ c n t = σ t := by sorry
