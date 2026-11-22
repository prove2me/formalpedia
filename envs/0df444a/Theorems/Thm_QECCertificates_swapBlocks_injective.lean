-- Prove2me | Theorems.Thm_QECCertificates_swapBlocks_injective
-- name    : QECCertificates.swapBlocks_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:10.892821+00:00
-- url     : https://prove2.me/theorems/ec3fdd39-bcb0-458a-8e1e-963c695e9406
-- title:
--   QECCertificates: swap Blocks injective
-- statement:
--   The block swap is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L40-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L40-L43

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.swapBlocks_injective {α β : Type*} : Function.Injective (swapBlocks (α := α) (β := β)) := by sorry
