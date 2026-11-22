-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_mulVec_eq_zero_iff
-- name    : QECCertificates.hgpHZ_mulVec_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:51.440631+00:00
-- url     : https://prove2.me/theorems/782c9547-b114-4697-90aa-04fb638a6630
-- title:
--   QECCertificates: hgp HZ mul Vec eq zero iff
-- statement:
--   **Compression identity (Z side)**: $H_Z v = 0 \iff U\,H_2^\top = H_1^\top\,R$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L197-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L197-L213

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

theorem QECCertificates.hgpHZ_mulVec_eq_zero_iff (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔ blockL v * H₂.transpose = H₁.transpose * blockR v := by sorry
