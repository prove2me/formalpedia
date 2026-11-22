-- Prove2me | Theorems.Thm_QECCertificates_wtRec_eq_card_support
-- name    : QECCertificates.wtRec_eq_card_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:22.722273+00:00
-- url     : https://prove2.me/theorems/c0bf0405-26aa-4946-8ea4-7c1c05398544
-- title:
--   QECCertificates: wt Rec eq card support
-- statement:
--   `wtRec` is the size of the support (agreeing with `support` and `hammingNorm`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L257-L283
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L257-L283

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.wtRec_eq_card_support (v : Vec n) : wtRec n v = (support v).card := by sorry
