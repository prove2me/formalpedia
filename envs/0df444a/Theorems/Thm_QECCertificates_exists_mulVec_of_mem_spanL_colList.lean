-- Prove2me | Theorems.Thm_QECCertificates_exists_mulVec_of_mem_spanL_colList
-- name    : QECCertificates.exists_mulVec_of_mem_spanL_colList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:11.164266+00:00
-- url     : https://prove2.me/theorems/09e77d23-22de-4df2-a3b1-f3d83ecec140
-- title:
--   QECCertificates: exists mul Vec of mem span L col List
-- statement:
--   A vector in the column span is the image of right multiplication (the columns are the images
--       of the
--   unit vectors under that map).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L97-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L97-L124

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

theorem QECCertificates.exists_mulVec_of_mem_spanL_colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec m} (h : y ∈ spanL (colList M)) : ∃ x : Vec k, M *ᵥ x = y := by sorry
