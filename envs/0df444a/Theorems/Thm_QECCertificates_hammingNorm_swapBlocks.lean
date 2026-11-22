-- Prove2me | Theorems.Thm_QECCertificates_hammingNorm_swapBlocks
-- name    : QECCertificates.hammingNorm_swapBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:11.327815+00:00
-- url     : https://prove2.me/theorems/0c0c7020-9e1e-4521-87aa-13296bcdde30
-- title:
--   QECCertificates: hamming Norm swap Blocks
-- statement:
--   **The block swap preserves weight**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L46-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L46-L59

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

theorem QECCertificates.hammingNorm_swapBlocks
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hammingNorm (fun c => v (swapBlocks c)) = hammingNorm v := by sorry
