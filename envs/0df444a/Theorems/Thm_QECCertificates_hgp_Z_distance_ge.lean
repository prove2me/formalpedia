-- Prove2me | Theorems.Thm_QECCertificates_hgp_Z_distance_ge
-- name    : QECCertificates.hgp_Z_distance_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:37.412066+00:00
-- url     : https://prove2.me/theorems/2133ec40-25ea-4518-b8b8-9472df285328
-- title:
--   QECCertificates: hgp Z distance ge
-- statement:
--   **The Z-distance lower bound for HGP**: a nonzero Z-type operator outside the row
--   space of `H_X` has weight at least $\min(d_1^\top, d_2)$, the smaller of the **transpose-code
--   distance** and the distance of the right code.
--
--   The proof swaps the blocks of $v$ and applies the X-side theorem to the inputs
--   $(H_1^\top,H_2^\top)$. Transposition interchanges $d_1\leftrightarrow d_1^\top$ and
--   $d_2^\top\leftrightarrow d_2$, so the $\min(d_1,d_2^\top)$ of the X side is
--   $\min(d_1^\top,d_2)$ here.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaningDual.lean#L62-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaningDual.lean#L62-L76

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

theorem QECCertificates.hgp_Z_distance_ge (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₁T d₂ : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w) :
    min d₁T d₂ ≤ hammingNorm v := by sorry
