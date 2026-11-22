-- Prove2me | Theorems.Thm_QECCertificates_mul_inv_eq_one_iff
-- name    : QECCertificates.mul_inv_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:36.417662+00:00
-- url     : https://prove2.me/theorems/540e83a5-dbce-40a9-a2a5-ec64fbe065ca
-- title:
--   QECCertificates: mul inv eq one iff
-- statement:
--   `σ * τ⁻¹ = 1 ↔ σ = τ` (shared by the two lemmas for constant seeds).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L120-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L120-L125

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.mul_inv_eq_one_iff (σ τ : G) : σ * τ⁻¹ = 1 ↔ σ = τ := by sorry
