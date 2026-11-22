-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_row_eq_swap
-- name    : QECCertificates.hgpHZ_row_eq_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:47.255536+00:00
-- url     : https://prove2.me/theorems/c8df79ae-2554-4694-bc20-0dfac72a02cf
-- title:
--   QECCertificates: hgp HZ row eq swap
-- statement:
--   **The row identity**: row $x$ of $H_Z(H_1^\top,H_2^\top)$ is row $x$ of
--   $H_X(H_1,H_2)$ followed by the block swap, entrywise, straight from the transpose-code
--   relation of part two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L66-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L66-L74

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.hgpHZ_row_eq_swap (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin n₁ × Fin r₂) :
    hgpHZ H₁ H₂ x = fun c => hgpHX H₁.transpose H₂.transpose x (swapBlocks c) := by sorry
