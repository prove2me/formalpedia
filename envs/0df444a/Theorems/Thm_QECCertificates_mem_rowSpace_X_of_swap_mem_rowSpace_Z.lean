-- Prove2me | Theorems.Thm_QECCertificates_mem_rowSpace_X_of_swap_mem_rowSpace_Z
-- name    : QECCertificates.mem_rowSpace_X_of_swap_mem_rowSpace_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:29.600623+00:00
-- url     : https://prove2.me/theorems/a9eb5de7-2555-4ad8-8cbb-069a6522666b
-- title:
--   QECCertificates: mem row Space X of swap mem row Space Z
-- statement:
--   **The correspondence of row spaces**: for a vector $w$ that after the swap lies in the
--   row space of $H_Z(H_1^\top,H_2^\top)$, swapping once more puts it in the row space of
--   $H_X(H_1,H_2)$; for $v := w\circ\text{swap}$ this says
--   $v\in\mathrm{row}H_X(H_1,H_2)$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L113-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPTranspose.lean#L113-L164

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

theorem QECCertificates.mem_rowSpace_X_of_swap_mem_rowSpace_Z (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (h : (fun c => v (swapBlocks c)) ∈ (hgpHZ H₁.transpose H₂.transpose).certificateRowSpace) :
    v ∈ (hgpHX H₁ H₂).certificateRowSpace := by sorry
