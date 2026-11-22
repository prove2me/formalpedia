-- Prove2me | Theorems.Thm_QECCertificates_hgp_hammingNorm_ge_of_pure_right
-- name    : QECCertificates.hgp_hammingNorm_ge_of_pure_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:56.107547+00:00
-- url     : https://prove2.me/theorems/5536ecc0-a9d5-4e78-95f2-eda9cd7b00be
-- title:
--   QECCertificates: hgp hamming Norm ge of pure right
-- statement:
--   **Single-block weight lower bound (right)**: an X-type operator supported only in the
--   right block has weight at least the distance of `ker H₂ᵀ` (the **transpose-code distance**
--   `d₂ᵀ`), which is exactly why the transpose code appears in the lower bound formula.
--
--   Every row `r_i` of the right block satisfies `H₂ᵀ r_i = 0` (compression identity plus
--   `blockL v = 0`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L288-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L288-L319

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

theorem QECCertificates.hgp_hammingNorm_ge_of_pure_right {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hL : blockL v = 0) {d : ℕ}
    (hd : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d ≤ hammingNorm w)
    (hR : blockR v ≠ 0) : d ≤ hammingNorm v := by sorry
