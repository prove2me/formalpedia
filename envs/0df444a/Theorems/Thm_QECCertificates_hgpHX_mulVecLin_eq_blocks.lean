-- Prove2me | Theorems.Thm_QECCertificates_hgpHX_mulVecLin_eq_blocks
-- name    : QECCertificates.hgpHX_mulVecLin_eq_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:35.192815+00:00
-- url     : https://prove2.me/theorems/e161fdbc-9501-42da-a0b1-5afd57a71c31
-- title:
--   QECCertificates: hgp HX mul Vec Lin eq blocks
-- statement:
--   **The block action of `H_X`**: `H_X v = A·U + R·B` (with `U = blkL v` and `R = blkR v`),
--   the "sum of matrices" form of the compression identity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L161-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPKunneth.lean#L161-L169

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHX_mulVecLin_eq_blocks (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    (hgpHX A B).mulVecLin v
      = mulLeft (s := n₂) A (blkL v) + mulRight (p := r₁) B (blkR v) := by sorry
