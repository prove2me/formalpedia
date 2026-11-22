-- Prove2me | Theorems.Thm_QECCertificates_LinearMap_ker_eq_spanL_kerBasis_ofFn
-- name    : QECCertificates.LinearMap.ker_eq_spanL_kerBasis_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:30.733027+00:00
-- url     : https://prove2.me/theorems/9bbe430e-e2af-4dd1-8150-63ebfcf60f7e
-- title:
--   Linear Map: ker eq span L ker Basis of Fn
-- statement:
--   **Main theorem for external use (LeanQEC interface version)**: the kernel of a
--   parity-check matrix `M` equals the space spanned by the kernel generators. The generators
--   are read directly off the list of rows of `M` by the trusted row reduction, and the whole
--   procedure closes inside the kernel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L459-L462
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L459-L462

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.LinearMap.ker_eq_spanL_kerBasis_ofFn {m : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = spanL (kerBasis (rowReduce (List.ofFn fun i => M i))) := by sorry
