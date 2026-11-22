-- Prove2me | Theorems.Thm_QECCertificates_lp2HZ_inl
-- name    : QECCertificates.lp2HZ_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:59.132699+00:00
-- url     : https://prove2.me/theorems/f54a7fc5-fbaa-49b9-baf2-ee38529a2167
-- title:
--   QECCertificates: lp2 HZ inl
-- statement:
--   The QECCertificates construction uses the lp2 HZ inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L324-L325
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L324-L325

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp2HZ_inl (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inl τ) = rightMulMat b τ σ := by sorry
