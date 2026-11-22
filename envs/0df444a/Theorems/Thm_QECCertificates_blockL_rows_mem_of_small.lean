-- Prove2me | Theorems.Thm_QECCertificates_blockL_rows_mem_of_small
-- name    : QECCertificates.blockL_rows_mem_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:58.355946+00:00
-- url     : https://prove2.me/theorems/f34654bd-3e5c-41b7-a037-19fe7b462cc9
-- title:
--   QECCertificates: block L rows mem of small
-- statement:
--   **Row cleaning**: if $|v| < d_1$, every row of `blockL v` lies in the row space of `H₂`.
--
--   The proof uses the **matrix-level** form of the compression identity: if some row has nonzero dot
--   product with `z ∈ ker H₂`, then `blockL v *ᵥ z ≠ 0`, whereas
--   `H₁ *ᵥ (blockL v *ᵥ z) = (H₁ * blockL v) *ᵥ z = (blockR v * H₂) *ᵥ z = blockR v *ᵥ (H₂ *ᵥ z) = 0`,
--   which contradicts `d₁`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L375-L397
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L375-L397

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

theorem QECCertificates.blockL_rows_mem_of_small
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₁) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by sorry
