-- Prove2me | Theorems.Thm_QECCertificates_lp2HX_inr
-- name    : QECCertificates.lp2HX_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:54.745881+00:00
-- url     : https://prove2.me/theorems/1a3e8177-cac4-45cd-bd28-c5785975112b
-- title:
--   QECCertificates: lp2 HX inr
-- statement:
--   The QECCertificates construction uses the lp2 HX inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L321-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L321-L322

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp2HX_inr (a b : G → ZMod 2) (σ τ : G) :
    lp2HX a b σ (Sum.inr τ) = rightMulMat b σ τ := by sorry
