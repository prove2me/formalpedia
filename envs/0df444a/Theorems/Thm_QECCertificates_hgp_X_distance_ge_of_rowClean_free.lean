-- Prove2me | Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_rowClean_free
-- name    : QECCertificates.hgp_X_distance_ge_of_rowClean_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:02.969218+00:00
-- url     : https://prove2.me/theorems/6f4cf2b2-25ab-48c8-8189-f1fc609e917b
-- title:
--   QECCertificates: hgp X distance ge of row Clean free
-- statement:
--   **Cleaning lower bound with row cleaning free**: as soon as the rows of `blockL v` lie in the
--       row
--   space of $H_2$ **unconditionally**, the single factor $d_2^\top$ suffices; the rest is word for
--   word `hgp_X_distance_ge` (column cleaning still uses $|v|<d_2^\top$).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L715-L754
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L715-L754

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

theorem QECCertificates.hgp_X_distance_ge_of_rowClean_free
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hrow : ∀ a, (fun b => blockL v a b) ∈ spanL (matRowList H₂)) :
    d₂T ≤ hammingNorm v := by sorry
