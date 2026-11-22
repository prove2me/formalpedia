-- Prove2me | Theorems.Thm_QECCertificates_lp2HZ_inr
-- name    : QECCertificates.lp2HZ_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:58.77538+00:00
-- url     : https://prove2.me/theorems/03a0f8fe-004f-4831-99ed-066381f5a60c
-- title:
--   QECCertificates: lp2 HZ inr
-- statement:
--   The QECCertificates construction uses the lp2 HZ inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L327-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L327-L328

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp2HZ_inr (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inr τ) = leftMulMat a τ σ := by sorry
