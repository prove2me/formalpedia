-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainsFrom_snd_ge
-- name    : QECCertificates.LRAT.chainsFrom_snd_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:17.994847+00:00
-- url     : https://prove2.me/theorems/2f1e8744-ec03-455b-a93d-b5f1b6091e00
-- title:
--   LRAT: chains From snd ge
-- statement:
--   The exit counter of a sequence of chains never decreases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L931-L941
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L931-L941

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainsFrom_snd_ge {f : Nat → Nat} : ∀ (rows : List (List Nat)) (c : Nat),
    c ≤ (chainsFrom f rows c).2 := by sorry
