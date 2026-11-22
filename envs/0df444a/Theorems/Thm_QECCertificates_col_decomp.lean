-- Prove2me | Theorems.Thm_QECCertificates_col_decomp
-- name    : QECCertificates.col_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:20.568457+00:00
-- url     : https://prove2.me/theorems/3746accd-e731-4361-8f90-a2191c441b70
-- title:
--   QECCertificates: col decomp
-- statement:
--   **Column decomposition** (read back from the elimination): if every column of `M` lies in the
--       span
--   of the row list `c`, the pivot rows of the elimination output give an explicit set of coefficients:
--   `M i j = Σ_{ri} M ri.2 j * ri.1 i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L436-L444
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L436-L444

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

theorem QECCertificates.col_decomp {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (c : List (Vec m))
    (hc : ∀ j : Fin k, (fun i => M i j) ∈ spanL c) (i : Fin m) (j : Fin k) :
    M i j = ∑ ri ∈ (rowReduce c).toFinset, (M ri.2 j) * (ri.1 i) := by sorry
