-- Prove2me | Theorems.Thm_QECCertificates_wtRec_eq_hammingNorm
-- name    : QECCertificates.wtRec_eq_hammingNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:52.372636+00:00
-- url     : https://prove2.me/theorems/eff6812c-c00b-4a44-8f92-76261bb4b70f
-- title:
--   QECCertificates: wt Rec eq hamming Norm
-- statement:
--   `wtRec` agrees with the standard `hammingNorm` (the bridge to the public
--   interface).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L287-L288
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L287-L288

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.wtRec_eq_hammingNorm (v : Vec n) : wtRec n v = hammingNorm v := by sorry
