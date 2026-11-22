-- Prove2me | Theorems.Thm_QECCertificates_Pauli_symp_mul
-- name    : QECCertificates.Pauli.symp_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:34.63462+00:00
-- url     : https://prove2.me/theorems/c57db75e-8a41-40b5-bb65-a33d9edca8ac
-- title:
--   Pauli: symp mul
-- statement:
--   **Translation theorem, single site**: single-site multiplication carries over to
--   coordinatewise addition of symplectic encodings.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L128-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L128-L129

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

theorem QECCertificates.Pauli.symp_mul (p q : Pauli) : symp (mul p q) = symp p + symp q := by sorry
