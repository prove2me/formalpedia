-- Prove2me | Theorems.Thm_QECCertificates_colDot_hammingNorm_le
-- name    : QECCertificates.colDot_hammingNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:18.292406+00:00
-- url     : https://prove2.me/theorems/c167f6a5-bbe2-4f48-b89f-46562124a2a3
-- title:
--   QECCertificates: col Dot hamming Norm le
-- statement:
--   The weight after column-wise dot products is at most the weight of the whole vector (every
--       column
--   that is nonzero contributes one support point).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L334-L365
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L334-L365

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

theorem QECCertificates.colDot_hammingNorm_le
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (w : Vec r₁) :
    hammingNorm (fun t : Fin r₂ => ∑ i, v (Sum.inr (i, t)) * w i) ≤ hammingNorm v := by sorry
