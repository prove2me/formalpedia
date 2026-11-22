-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_mulVec_apply
-- name    : QECCertificates.hgpHZ_mulVec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:05.19296+00:00
-- url     : https://prove2.me/theorems/103e9b41-7c71-4fd2-b5b0-fa50b556fc04
-- title:
--   QECCertificates: hgp HZ mul Vec apply
-- statement:
--   **Z side, entrywise**: `(H_Z v)_{(a,d)} = (U · H_2ᵀ)_{ad} + (H_1ᵀ · R)_{ad}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L153-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L153-L172

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

theorem QECCertificates.hgpHZ_mulVec_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (a : Fin n₁) (d : Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) (a, d) = (blockL v * H₂.transpose) a d + (H₁.transpose * blockR v) a d := by sorry
