-- Prove2me | Theorems.Thm_QECCertificates_hgpHZ_transpose_inputs_apply
-- name    : QECCertificates.hgpHZ_transpose_inputs_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:13.235191+00:00
-- url     : https://prove2.me/theorems/287b9a1f-c207-4f21-9430-732112c36fd4
-- title:
--   QECCertificates: hgp HZ transpose inputs apply
-- statement:
--   **Transpose-code relation**: the Z parity-check matrix obtained from the transposed
--   inputs agrees entrywise with the original X parity-check matrix, under the column
--   relabelling that swaps the two blocks. Hence `HGP(H₁ᵀ, H₂ᵀ)` is the transpose code of
--   `HGP(H₁, H₂)`, and the X-side and Z-side distance analyses are two applications of one
--   and the same argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L222-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCompression.lean#L222-L229

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

theorem QECCertificates.hgpHZ_transpose_inputs_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin r₁ × Fin n₂)
    (c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂)) :
    hgpHZ H₁.transpose H₂.transpose x c
      = hgpHX H₁ H₂ x (Equiv.sumComm _ _ c) := by sorry
