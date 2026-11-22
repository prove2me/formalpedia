-- Prove2me | Theorems.Thm_QECCertificates_PauliExpr_commutes_iff_symplectic
-- name    : QECCertificates.PauliExpr.commutes_iff_symplectic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:25.88747+00:00
-- url     : https://prove2.me/theorems/f7907f4e-a8c0-420b-b322-09651b8d525f
-- title:
--   Pauli Expr: commutes iff symplectic
-- statement:
--   **The translation theorem for commutation, tree form**: commutation at the tree layer
--   if and only if the symplectic inner product vanishes at the decision layer.
--
--   This is the main public criterion of this module: every structural statement about
--   stabilizer codes, whether an element lies in the stabilizer group, whether a logical
--   operator commutes with the stabilizers, or whether a distance candidate commutes with the
--   checks, reduces to it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L259-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L259-L261

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.PauliExpr

theorem QECCertificates.PauliExpr.commutes_iff_symplectic (a b : PauliExpr n) :
    commutes a b ↔ (toSymp a).1 ⬝ᵥ (toSymp b).2 + (toSymp b).1 ⬝ᵥ (toSymp a).2 = 0 := by sorry
