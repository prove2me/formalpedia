-- Prove2me | Theorems.Thm_QECCertificates_blockR_cols_mem_of_small
-- name    : QECCertificates.blockR_cols_mem_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:04.686428+00:00
-- url     : https://prove2.me/theorems/7bb1ec48-aafc-4642-ad89-e55e05b7b686
-- title:
--   QECCertificates: block R cols mem of small
-- statement:
--   **Column cleaning**: if $|v| < d_2^\top$, every column of `blockR v` lies in the column space of
--   `H₁`.
--
--   The dual matrix-level argument: the transposed-code identity for `(blockR v)ᵀ *ᵥ w` gives
--   `H₂ᵀ *ᵥ ((blockR v)ᵀ *ᵥ w) = (blockL v)ᵀ *ᵥ (H₁ᵀ *ᵥ w) = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L404-L428
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L404-L428

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

theorem QECCertificates.blockR_cols_mem_of_small
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₂T) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by sorry
