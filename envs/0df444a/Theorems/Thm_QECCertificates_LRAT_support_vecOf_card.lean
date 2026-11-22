-- Prove2me | Theorems.Thm_QECCertificates_LRAT_support_vecOf_card
-- name    : QECCertificates.LRAT.support_vecOf_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:34.080228+00:00
-- url     : https://prove2.me/theorems/32da87a6-65a3-4c0f-8016-5b9dda761506
-- title:
--   LRAT: support vec Of card
-- statement:
--   The support size of `vecOf` is exactly the count of the assignment: the two readings give the
--   same
--   weight.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L51-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L51-L72

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.support_vecOf_card (σ : Assign) (n : ℕ) :
    (support (vecOf σ n)).card = cntS σ (List.range n) := by sorry
