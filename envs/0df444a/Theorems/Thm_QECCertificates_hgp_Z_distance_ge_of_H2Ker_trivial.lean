-- Prove2me | Theorems.Thm_QECCertificates_hgp_Z_distance_ge_of_H2Ker_trivial
-- name    : QECCertificates.hgp_Z_distance_ge_of_H2Ker_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:35.674876+00:00
-- url     : https://prove2.me/theorems/65848364-011d-4fe1-9c29-ad85002bbcaa
-- title:
--   QECCertificates: hgp Z distance ge of H2 Ker trivial
-- statement:
--   **A lower bound on $d_Z$, the $\ker H_2=0$ branch**: when $H_2$ is injective, the
--   single factor $d_1^\top$ suffices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaningDual.lean#L152-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaningDual.lean#L152-L166

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaningDual
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgp_Z_distance_ge_of_H2Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₁T : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) :
    d₁T ≤ hammingNorm v := by sorry
