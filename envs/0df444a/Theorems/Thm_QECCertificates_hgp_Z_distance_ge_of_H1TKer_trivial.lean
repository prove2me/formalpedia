-- Prove2me | Theorems.Thm_QECCertificates_hgp_Z_distance_ge_of_H1TKer_trivial
-- name    : QECCertificates.hgp_Z_distance_ge_of_H1TKer_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:11.535272+00:00
-- url     : https://prove2.me/theorems/432b8f63-ad02-46bb-be09-3b357d379ab9
-- title:
--   QECCertificates: hgp Z distance ge of H1 TKer trivial
-- statement:
--   **A lower bound on $d_Z$, the $\ker H_1^\top=0$ branch**: when $H_1^\top$ is
--   injective, the single factor $d_2$ suffices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaningDual.lean#L134-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaningDual.lean#L134-L148

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

theorem QECCertificates.hgp_Z_distance_ge_of_H1TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₂ : ℕ}
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₂ ≤ hammingNorm v := by sorry
