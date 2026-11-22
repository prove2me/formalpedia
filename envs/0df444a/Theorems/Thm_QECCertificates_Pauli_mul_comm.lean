-- Prove2me | Theorems.Thm_QECCertificates_Pauli_mul_comm
-- name    : QECCertificates.Pauli.mul_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:48.237467+00:00
-- url     : https://prove2.me/theorems/13a65966-51e0-43d3-9600-b505100e1d73
-- title:
--   Pauli: mul comm
-- statement:
--   The Pauli construction uses the mul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L122-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L122-L122

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

theorem QECCertificates.Pauli.mul_comm (p q : Pauli) : mul p q = mul q p := by sorry
