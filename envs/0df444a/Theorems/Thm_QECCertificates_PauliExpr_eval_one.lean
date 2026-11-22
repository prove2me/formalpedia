-- Prove2me | Theorems.Thm_QECCertificates_PauliExpr_eval_one
-- name    : QECCertificates.PauliExpr.eval_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:22.935944+00:00
-- url     : https://prove2.me/theorems/5b854d3f-7656-4b41-bfb5-e25da35bf753
-- title:
--   Pauli Expr: eval one
-- statement:
--   The Pauli Expr construction uses the eval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L218-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L218-L218

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

theorem QECCertificates.PauliExpr.eval_one : eval (.one : PauliExpr n) = fun _ => Pauli.I := by sorry

attribute [defeq] QECCertificates.PauliExpr.eval_one
