-- Prove2me | Theorems.Thm_QECCertificates_mulVec_mem_spanL_colList
-- name    : QECCertificates.mulVec_mem_spanL_colList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:28.224432+00:00
-- url     : https://prove2.me/theorems/d131bd4d-2668-4f2a-8a2b-b26fb3737d1b
-- title:
--   QECCertificates: mul Vec mem span L col List
-- statement:
--   The image of right multiplication lies in the column span.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L127-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L127-L138

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

theorem QECCertificates.mulVec_mem_spanL_colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (x : Vec k) :
    M *ᵥ x ∈ spanL (colList M) := by sorry
