-- Prove2me | Theorems.Thm_QECCertificates_mulVec_swap_eq
-- name    : QECCertificates.mulVec_swap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:14.637365+00:00
-- url     : https://prove2.me/theorems/d65c9134-1ad6-4367-a7fa-cd708a62ef70
-- title:
--   QECCertificates: mul Vec swap eq
-- statement:
--   **The row identity for the dot products**: the two kernel conditions are equal row by
--   row, not merely vanishing together.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L78-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L78-L94

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

theorem QECCertificates.mulVec_swap_eq (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (x : Fin n₁ × Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) x
      = (hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c))) x := by sorry
