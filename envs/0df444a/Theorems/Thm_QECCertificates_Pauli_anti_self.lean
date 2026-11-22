-- Prove2me | Theorems.Thm_QECCertificates_Pauli_anti_self
-- name    : QECCertificates.Pauli.anti_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:46.71317+00:00
-- url     : https://prove2.me/theorems/117bb867-8469-4835-9ec6-19892ce7a1a5
-- title:
--   Pauli: anti self
-- statement:
--   The Pauli construction uses the anti self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L131-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L131-L131

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.Pauli

theorem QECCertificates.Pauli.anti_self (p : Pauli) : anti p p = 0 := by sorry
