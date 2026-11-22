-- Prove2me | Theorems.Thm_QECCertificates_PauliExpr_toSymp_atom
-- name    : QECCertificates.PauliExpr.toSymp_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:21.760555+00:00
-- url     : https://prove2.me/theorems/54c46ddf-87a7-42aa-9f00-c16b6cb83889
-- title:
--   Pauli Expr: to Symp atom
-- statement:
--   Translation of a leaf: only position `i` is nonzero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L240-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L240-L246

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

theorem QECCertificates.PauliExpr.toSymp_atom (i : Fin n) (p : Pauli) :
    toSymp (.atom i p)
      = ((fun j => if j = i then (Pauli.symp p).1 else 0),
         (fun j => if j = i then (Pauli.symp p).2 else 0)) := by sorry
