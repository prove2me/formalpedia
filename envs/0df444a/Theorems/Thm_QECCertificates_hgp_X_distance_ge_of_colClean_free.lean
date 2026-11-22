-- Prove2me | Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_colClean_free
-- name    : QECCertificates.hgp_X_distance_ge_of_colClean_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:12.576011+00:00
-- url     : https://prove2.me/theorems/3e7797ef-5768-4f5c-937e-5e9fe2f88b37
-- title:
--   QECCertificates: hgp X distance ge of col Clean free
-- statement:
--   **Cleaning lower bound with column cleaning free**: as soon as the columns of `blockR v` lie in
--   the column space of $H_1$ **unconditionally**, the single factor $d_1$ suffices (row cleaning still
--   uses $|v|<d_1$).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L759-L799
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L759-L799

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgp_X_distance_ge_of_colClean_free
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hcol : ∀ t, (fun i => blockR v i t) ∈ spanL (colList H₁)) :
    d₁ ≤ hammingNorm v := by sorry
