-- Prove2me | Theorems.Thm_QECCertificates_sympWord_fst
-- name    : QECCertificates.sympWord_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:20.641881+00:00
-- url     : https://prove2.me/theorems/e0867171-1e32-4dea-b6db-4c97af426656
-- title:
--   QECCertificates: symp Word fst
-- statement:
--   The QECCertificates construction uses the symp Word fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L152-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L152-L152

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.sympWord_fst (w : PauliWord n) : (sympWord w).1 = fun i => (Pauli.symp (w i)).1 := by sorry

attribute [defeq] QECCertificates.sympWord_fst
