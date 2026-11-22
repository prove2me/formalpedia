-- Prove2me | Theorems.Thm_QECCertificates_Pauli_anti_eq_symp
-- name    : QECCertificates.Pauli.anti_eq_symp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:39.857563+00:00
-- url     : https://prove2.me/theorems/05f4ae8c-b577-4088-8524-8ac695c41985
-- title:
--   Pauli: anti eq symp
-- statement:
--   **Translation theorem, single-site commutation criterion**: the anticommutation
--   indicator equals exactly the single-site symplectic inner product `(z_p x_q + z_q x_p)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L136-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L136-L138

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

theorem QECCertificates.Pauli.anti_eq_symp (p q : Pauli) :
    anti p q = (symp p).1 * (symp q).2 + (symp q).1 * (symp p).2 := by sorry
