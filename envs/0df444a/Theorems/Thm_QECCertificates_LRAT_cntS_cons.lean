-- Prove2me | Theorems.Thm_QECCertificates_LRAT_cntS_cons
-- name    : QECCertificates.LRAT.cntS_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:33.074581+00:00
-- url     : https://prove2.me/theorems/79d6a11c-df4d-4513-acaf-953b4abef681
-- title:
--   LRAT: cnt S cons
-- statement:
--   The recursion for `cntS` (in this version the predicate of `List.filter` is `Bool`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L77-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L77-L80

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.cntS_cons (σ : Assign) (j : Nat) (s : List Nat) :
    cntS σ (j :: s) = (if σ j then 1 else 0) + cntS σ s := by sorry
