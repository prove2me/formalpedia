-- Prove2me | Theorems.Thm_QECCertificates_sum_smul_hgpHZ_apply
-- name    : QECCertificates.sum_smul_hgpHZ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:24.540074+00:00
-- url     : https://prove2.me/theorems/51191cee-ed2b-4f3d-a103-2d4cc21fdd41
-- title:
--   QECCertificates: sum smul hgp HZ apply
-- statement:
--   A vector of the form `(C H₂, H₁ C)` is a linear combination of the rows of `H_Z` (computed
--   entrywise).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L499-L542
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L499-L542

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

theorem QECCertificates.sum_smul_hgpHZ_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (C : Matrix (Fin n₁) (Fin r₂) (ZMod 2))
    (c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) :
    (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p) c
      = Sum.elim (fun ab => (C * H₂) ab.1 ab.2) (fun st => (H₁ * C) st.1 st.2) c := by sorry
