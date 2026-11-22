-- Prove2me | Theorems.Thm_QECCertificates_Matrix_rowSpace_eq_spanL_ofFn
-- name    : QECCertificates.Matrix.rowSpace_eq_spanL_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:00.005789+00:00
-- url     : https://prove2.me/theorems/f0ab92bb-790e-4783-87b5-cc63912a9f16
-- title:
--   Matrix: row Space eq span L of Fn
-- statement:
--   **Bridge to LeanQEC**: `Matrix.certificateRowSpace M` (that is, `Submodule.span (Set.range M)`)
--   equals the `spanL` of the row list of `M`. The row-space theorems of LeanQEC therefore
--   apply directly to the row lists of this package.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L195-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L195-L202

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.Matrix.rowSpace_eq_spanL_ofFn {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.certificateRowSpace = spanL (List.ofFn fun i => M i) := by sorry
