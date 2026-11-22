-- Prove2me | Theorems.Thm_QECCertificates_blockR_apply
-- name    : QECCertificates.blockR_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:36.667662+00:00
-- url     : https://prove2.me/theorems/bfc8a332-9d47-4325-9275-d505bce23fae
-- title:
--   QECCertificates: block R apply
-- statement:
--   The QECCertificates construction uses the block R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L88-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L88-L89

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.blockR_apply (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (s : Fin r₁) (t : Fin r₂) : blockR v s t = v (Sum.inr (s, t)) := by sorry

attribute [defeq] QECCertificates.blockR_apply
