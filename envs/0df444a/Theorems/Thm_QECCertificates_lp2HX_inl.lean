-- Prove2me | Theorems.Thm_QECCertificates_lp2HX_inl
-- name    : QECCertificates.lp2HX_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:56.746129+00:00
-- url     : https://prove2.me/theorems/2e58e626-4294-4add-bb65-6c5d5fc90485
-- title:
--   QECCertificates: lp2 HX inl
-- statement:
--   The QECCertificates construction uses the lp2 HX inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L318-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L318-L319

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp2HX_inl (a b : G → ZMod 2) (σ τ : G) :
    lp2HX a b σ (Sum.inl τ) = leftMulMat a σ τ := by sorry
