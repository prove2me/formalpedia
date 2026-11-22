-- Prove2me | Theorems.Thm_QECCertificates_blockR_cols_mem_of_adjoint_ker_trivial
-- name    : QECCertificates.blockR_cols_mem_of_adjoint_ker_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:42.654976+00:00
-- url     : https://prove2.me/theorems/4537ca78-4699-4ec3-bdf7-96e3e6efcd46
-- title:
--   QECCertificates: block R cols mem of adjoint ker trivial
-- statement:
--   **Column cleaning (branch $\ker H_1^\top=0$)**: here the columns of $H_1$ already span the whole
--   of `Vec r₁`, so the conclusion holds **unconditionally**. (Again the compression identity is **not
--   needed**.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L678-L685
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L678-L685

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

theorem QECCertificates.blockR_cols_mem_of_adjoint_ker_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by sorry
