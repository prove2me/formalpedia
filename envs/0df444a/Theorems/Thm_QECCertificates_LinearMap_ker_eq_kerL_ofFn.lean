-- Prove2me | Theorems.Thm_QECCertificates_LinearMap_ker_eq_kerL_ofFn
-- name    : QECCertificates.LinearMap.ker_eq_kerL_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:13.468582+00:00
-- url     : https://prove2.me/theorems/75b17462-bf8d-463d-8e04-bce47ce2c1ee
-- title:
--   Linear Map: ker eq ker L of Fn
-- statement:
--   The kernel of a parity-check **matrix** (LeanQEC's `LinearMap.ker M.toLin'`) agrees
--   with the kernel of its list of rows. This bridge lets the row-space theorems already
--   available in LeanQEC act directly on `kerL` of this module.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L441-L453
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L441-L453

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.LinearMap.ker_eq_kerL_ofFn {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = kerL (List.ofFn fun i => M i) := by sorry
