-- Prove2me | Theorems.Thm_QECCertificates_leftMulMat_mul_rightMulMat
-- name    : QECCertificates.leftMulMat_mul_rightMulMat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:20.895566+00:00
-- url     : https://prove2.me/theorems/7e466792-f83e-4756-b15b-348eabc0858b
-- title:
--   QECCertificates: left Mul Mat mul right Mul Mat
-- statement:
--   **The two regular representations commute entrywise**: `L(a) * R(b) = R(b) * L(a)`.
--
--   This is the whole content of the CSS compatibility of LP (`lp_orthogonal` calls nothing else).
--   Entrywise, both sides equal $\sum_\mu a(\sigma\mu^{-1}\tau^{-1})\,b(\mu)$: the left-hand side is
--   reindexed by $\rho \mapsto \tau^{-1}\rho$ and the right-hand side by $\rho \mapsto \rho^{-1}\sigma$,
--   and the two then differ by one commutativity of multiplication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L141-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L141-L168

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.leftMulMat_mul_rightMulMat [Fintype G] (a b : G → ZMod 2) :
    leftMulMat a * rightMulMat b = rightMulMat b * leftMulMat a := by sorry
