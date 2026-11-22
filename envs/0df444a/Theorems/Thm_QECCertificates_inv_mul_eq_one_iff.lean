-- Prove2me | Theorems.Thm_QECCertificates_inv_mul_eq_one_iff
-- name    : QECCertificates.inv_mul_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:38.978811+00:00
-- url     : https://prove2.me/theorems/dd012b73-584b-42c0-8448-50f198523a20
-- title:
--   QECCertificates: inv mul eq one iff
-- statement:
--   `τ⁻¹ * σ = 1 ↔ σ = τ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L128-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L128-L133

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.inv_mul_eq_one_iff (σ τ : G) : τ⁻¹ * σ = 1 ↔ σ = τ := by sorry
