-- Prove2me | Theorems.Thm_QECCertificates_Pauli_mul_I_right
-- name    : QECCertificates.Pauli.mul_I_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:08.90166+00:00
-- url     : https://prove2.me/theorems/71e0b668-dc44-4d9e-8241-2486d5b871c4
-- title:
--   Pauli: mul I right
-- statement:
--   The Pauli construction uses the mul I right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L120-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L120-L120

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

theorem QECCertificates.Pauli.mul_I_right (p : Pauli) : mul p .I = p := by sorry
