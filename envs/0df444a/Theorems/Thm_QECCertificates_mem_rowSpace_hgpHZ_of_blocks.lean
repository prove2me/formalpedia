-- Prove2me | Theorems.Thm_QECCertificates_mem_rowSpace_hgpHZ_of_blocks
-- name    : QECCertificates.mem_rowSpace_hgpHZ_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:51.941792+00:00
-- url     : https://prove2.me/theorems/12abb7a1-b36a-4a35-a56b-0fdb87f10b69
-- title:
--   QECCertificates: mem row Space hgp HZ of blocks
-- statement:
--   A vector whose two blocks are `C H₂` and `H₁ C` lies in the row space of `H_Z` (the same
--       object as
--   `Matrix.certificateRowSpace` in LeanQEC).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L547-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L547-L565

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

theorem QECCertificates.mem_rowSpace_hgpHZ_of_blocks {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    {C : Matrix (Fin n₁) (Fin r₂) (ZMod 2)}
    (hU : blockL v = C * H₂) (hR : blockR v = H₁ * C) :
    v ∈ (hgpHZ H₁ H₂).certificateRowSpace := by sorry
