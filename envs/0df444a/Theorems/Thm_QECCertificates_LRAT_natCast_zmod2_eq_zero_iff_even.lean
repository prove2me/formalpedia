-- Prove2me | Theorems.Thm_QECCertificates_LRAT_natCast_zmod2_eq_zero_iff_even
-- name    : QECCertificates.LRAT.natCast_zmod2_eq_zero_iff_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:33.653104+00:00
-- url     : https://prove2.me/theorems/3817dde0-3a31-4cd6-b4c7-11a4faeb92f6
-- title:
--   LRAT: nat Cast zmod2 eq zero iff even
-- statement:
--   A natural number `c : ℕ` has image zero in `ZMod 2` if and only if `c` is even.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L100-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L100-L101

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.natCast_zmod2_eq_zero_iff_even (c : ℕ) : ((c : ZMod 2) = 0) ↔ Even c := by sorry
