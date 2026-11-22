-- Prove2me | Theorems.Thm_QECCertificates_PauliExpr_toSymp_mul
-- name    : QECCertificates.PauliExpr.toSymp_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:08.665025+00:00
-- url     : https://prove2.me/theorems/be7874ee-4f4c-4aae-a551-cbab05dac789
-- title:
--   Pauli Expr: to Symp mul
-- statement:
--   **The main translation theorem, a multiplicative homomorphism**: multiplication on
--   operator trees carries over to coordinatewise addition of symplectic vectors.
--
--   This is the content of "the two representations meet": the structural operation of the
--   tree layer, namely multiplication, is linear at the decision layer, so an expression on
--   trees can be translated as a whole to the vector layer and handed to the linear algebra
--   machinery of `QECCertificates.GF2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L233-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Pauli/Expr.lean#L233-L237

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.PauliExpr

theorem QECCertificates.PauliExpr.toSymp_mul (a b : PauliExpr n) : toSymp (.mul a b) = toSymp a + toSymp b := by sorry
