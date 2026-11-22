-- Prove2me | Theorems.Thm_QECCertificates_Pauli_mul_assoc
-- name    : QECCertificates.Pauli.mul_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:03.881013+00:00
-- url     : https://prove2.me/theorems/024cc1ec-46c2-49a7-a31c-1b294c554047
-- title:
--   Pauli: mul assoc
-- statement:
--   The Pauli construction uses the mul assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L123-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L123-L124

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

theorem QECCertificates.Pauli.mul_assoc (p q r : Pauli) : mul (mul p q) r = mul p (mul q r) := by sorry
