-- Prove2me | Theorems.Thm_QECCertificates_LRAT_even_one_add
-- name    : QECCertificates.LRAT.even_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:37.44351+00:00
-- url     : https://prove2.me/theorems/70d8a511-d583-4eeb-9a91-7adadcd6d0c4
-- title:
--   LRAT: even one add
-- statement:
--   Adding one flips parity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L83-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L83-L84

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.even_one_add (m : ℕ) : Even (1 + m) ↔ ¬ Even m := by sorry
