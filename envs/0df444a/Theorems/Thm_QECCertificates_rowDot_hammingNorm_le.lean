-- Prove2me | Theorems.Thm_QECCertificates_rowDot_hammingNorm_le
-- name    : QECCertificates.rowDot_hammingNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:22.923528+00:00
-- url     : https://prove2.me/theorems/da4128a7-9e08-4af3-8013-651e81255341
-- title:
--   QECCertificates: row Dot hamming Norm le
-- statement:
--   The weight after row-wise dot products is at most the weight of the whole vector (every row that
--   is nonzero contributes one support point).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L298-L329
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L298-L329

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

theorem QECCertificates.rowDot_hammingNorm_le
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (z : Vec n₂) :
    hammingNorm (fun a : Fin n₁ => ∑ b, v (Sum.inl (a, b)) * z b) ≤ hammingNorm v := by sorry
