-- Prove2me | Theorems.Thm_QECCertificates_commutesWord_iff_symplectic
-- name    : QECCertificates.commutesWord_iff_symplectic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:40.439744+00:00
-- url     : https://prove2.me/theorems/5a982070-1e53-4e3a-92ad-67551cb7c4d6
-- title:
--   QECCertificates: commutes Word iff symplectic
-- statement:
--   **The commutation criterion, word form**: commutation at the operator layer if and
--   only if the symplectic inner product vanishes at the decision layer.
--
--   The proof transports the single-site correspondence `anti_eq_symp` pointwise and then
--   splits the sum; "commutation" in the two layers is one and the same GF(2) quadratic form
--   written two ways.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L176-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L176-L187

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.commutesWord_iff_symplectic (u v : PauliWord n) :
    commutesWord u v ↔
      (sympWord u).1 ⬝ᵥ (sympWord v).2 + (sympWord v).1 ⬝ᵥ (sympWord u).2 = 0 := by sorry
