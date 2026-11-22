-- Prove2me | Theorems.Thm_QECCertificates_sympWord_snd
-- name    : QECCertificates.sympWord_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:22.994057+00:00
-- url     : https://prove2.me/theorems/322cd276-e660-49ad-b44a-e29808f42e2d
-- title:
--   QECCertificates: symp Word snd
-- statement:
--   The QECCertificates construction uses the symp Word snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L153-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L153-L153

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.sympWord_snd (w : PauliWord n) : (sympWord w).2 = fun i => (Pauli.symp (w i)).2 := by sorry

attribute [defeq] QECCertificates.sympWord_snd
