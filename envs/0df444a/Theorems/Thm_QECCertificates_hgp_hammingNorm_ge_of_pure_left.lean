-- Prove2me | Theorems.Thm_QECCertificates_hgp_hammingNorm_ge_of_pure_left
-- name    : QECCertificates.hgp_hammingNorm_ge_of_pure_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:53.083658+00:00
-- url     : https://prove2.me/theorems/bc436b62-e277-4638-889c-7d33fb9a7f77
-- title:
--   QECCertificates: hgp hamming Norm ge of pure left
-- statement:
--   **Single-block weight lower bound (left)**: an X-type operator supported only in the
--   left block has weight at least the left-code distance `d₁`.
--
--   Every column of the left block lies in `ker H₁` (compression identity plus `blockR v = 0`),
--   a nonzero column has weight at least `d₁`, and a single column weighs no more than the
--   whole vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L252-L280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L252-L280

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

theorem QECCertificates.hgp_hammingNorm_ge_of_pure_left {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hR : blockR v = 0) {d : ℕ}
    (hd : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d ≤ hammingNorm w)
    (hL : blockL v ≠ 0) : d ≤ hammingNorm v := by sorry
