-- Prove2me | Theorems.Thm_QECCertificates_PauliExpr_eval_mul
-- name    : QECCertificates.PauliExpr.eval_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:25.404804+00:00
-- url     : https://prove2.me/theorems/775d953a-8516-4bbe-bcd9-a6379ac03f3a
-- title:
--   Pauli Expr: eval mul
-- statement:
--   The Pauli Expr construction uses the eval mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L220-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L220-L221

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

theorem QECCertificates.PauliExpr.eval_mul (a b : PauliExpr n) :
    eval (.mul a b) = fun i => Pauli.mul (eval a i) (eval b i) := by sorry

attribute [defeq] QECCertificates.PauliExpr.eval_mul
