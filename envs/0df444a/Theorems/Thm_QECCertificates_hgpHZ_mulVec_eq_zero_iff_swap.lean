-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_mulVec_eq_zero_iff_swap
-- name    : QECCertificates.hgpHZ_mulVec_eq_zero_iff_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:18.228795+00:00
-- url     : https://prove2.me/theorems/9ec33976-1594-4a4f-9391-93ebe8f3d5e6
-- title:
--   QECCertificates: hgp HZ mul Vec eq zero iff swap
-- statement:
--   **The correspondence of kernels**: $v\in\ker H_Z(H_1,H_2)$ exactly when the swapped
--   $v$ lies in $\ker H_X(H_1^\top,H_2^\top)$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L98-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L98-L107

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

theorem QECCertificates.hgpHZ_mulVec_eq_zero_iff_swap (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔
      hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c)) = 0 := by sorry
