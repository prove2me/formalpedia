-- Prove2me | Theorems.Thm_QECCertificates_blockL_apply
-- name    : QECCertificates.blockL_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:39.077515+00:00
-- url     : https://prove2.me/theorems/f6eee953-9e44-41b6-bcab-ef4c39c4d0c7
-- title:
--   QECCertificates: block L apply
-- statement:
--   The QECCertificates construction uses the block L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L85-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L85-L86

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

theorem QECCertificates.blockL_apply (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (a : Fin n₁) (b : Fin n₂) : blockL v a b = v (Sum.inl (a, b)) := by sorry

attribute [defeq] QECCertificates.blockL_apply
