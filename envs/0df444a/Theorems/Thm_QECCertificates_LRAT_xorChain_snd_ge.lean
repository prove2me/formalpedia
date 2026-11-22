-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChain_snd_ge
-- name    : QECCertificates.LRAT.xorChain_snd_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:39.538813+00:00
-- url     : https://prove2.me/theorems/de6b99bc-2744-4971-8c44-fb99d2864fad
-- title:
--   LRAT: xor Chain snd ge
-- statement:
--   The exit counter of a chain never decreases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L921-L928
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L921-L928

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChain_snd_ge (xs : List Nat) (w : Bool) (c : Nat) :
    c ≤ (xorChain xs w c).2 := by sorry
