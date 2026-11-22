-- Prove2me | Theorems.Thm_QECCertificates_swapBlocks_swapBlocks
-- name    : QECCertificates.swapBlocks_swapBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:11.150091+00:00
-- url     : https://prove2.me/theorems/a81a344a-5d3a-436c-b8ed-41a62211e848
-- title:
--   QECCertificates: swap Blocks swap Blocks
-- statement:
--   The block swap is an involution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L36-L37
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L36-L37

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

theorem QECCertificates.swapBlocks_swapBlocks {α β : Type*} (c : α ⊕ β) : swapBlocks (swapBlocks c) = c := by sorry
