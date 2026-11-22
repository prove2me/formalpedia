-- Prove2me | Theorems.Thm_QECCertificates_preimage_spec
-- name    : QECCertificates.preimage_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:15.949813+00:00
-- url     : https://prove2.me/theorems/cdabc727-104f-434d-8236-6be3e143a672
-- title:
--   QECCertificates: preimage spec
-- statement:
--   The QECCertificates construction uses the preimage spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L184-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L184-L187

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.preimage_spec {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) {y : Vec m}
    (h : ∃ x : Vec k, M *ᵥ x = y) : M *ᵥ preimage M y = y := by sorry
