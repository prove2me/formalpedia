-- Prove2me | Theorems.Thm_QECCertificates_hgpHX_mulVec_apply
-- name    : QECCertificates.hgpHX_mulVec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:11.255737+00:00
-- url     : https://prove2.me/theorems/55a7a7d7-13a4-4dac-9dfc-33ecd254a76f
-- title:
--   QECCertificates: hgp HX mul Vec apply
-- statement:
--   **X side, entrywise**: `(H_X v)_{(i,j)} = (H_1 · U)_{ij} + (R · H_2)_{ij}`, where
--   `U = blockL v` and `R = blockR v`.
--
--   The two sums reduce by the **definitions** of `H_X`, `H_1 ⊗ I` and `I ⊗ H_2` (at the `rfl`
--   level), and one slicing lemma each then collapses the sum over the product index into a
--   sum over a single index.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L133-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L133-L150

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

theorem QECCertificates.hgpHX_mulVec_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (i : Fin r₁) (j : Fin n₂) :
    (hgpHX H₁ H₂ *ᵥ v) (i, j) = (H₁ * blockL v) i j + (blockR v * H₂) i j := by sorry
