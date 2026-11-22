-- Prove2me | Theorems.Thm_QECCertificates_Pauli_anti_comm
-- name    : QECCertificates.Pauli.anti_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:38.048868+00:00
-- url     : https://prove2.me/theorems/9ab49f0d-d8ca-4a75-8c1b-12e256380ac1
-- title:
--   Pauli: anti comm
-- statement:
--   The Pauli construction uses the anti comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L132-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L132-L132

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

theorem QECCertificates.Pauli.anti_comm (p q : Pauli) : anti p q = anti q p := by sorry
