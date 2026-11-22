-- Prove2me | Theorems.Thm_QECCertificates_LRAT_all_of_mem_ne_nil
-- name    : QECCertificates.LRAT.all_of_mem_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:45.019406+00:00
-- url     : https://prove2.me/theorems/0e22c9f1-66d2-425e-86bb-d1bdb55e8874
-- title:
--   LRAT: all of mem ne nil
-- statement:
--   As above, converting to "the support lists are nonempty".
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L247-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L247-L249

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.all_of_mem_ne_nil {L : List (List Nat)}
    (h : (L.all fun r => decide (r ≠ [])) = true) : ∀ r ∈ L, r ≠ [] := by sorry
