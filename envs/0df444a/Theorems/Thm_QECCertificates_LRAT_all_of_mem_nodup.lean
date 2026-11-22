-- Prove2me | Theorems.Thm_QECCertificates_LRAT_all_of_mem_nodup
-- name    : QECCertificates.LRAT.all_of_mem_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:38.454809+00:00
-- url     : https://prove2.me/theorems/65f88cb0-b710-4bcd-b26d-95414efe75f8
-- title:
--   LRAT: all of mem nodup
-- statement:
--   As above, converting to "the support lists have no duplicates".
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L242-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L242-L244

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.all_of_mem_nodup {L : List (List Nat)}
    (h : (L.all fun r => decide r.Nodup) = true) : ∀ r ∈ L, r.Nodup := by sorry
