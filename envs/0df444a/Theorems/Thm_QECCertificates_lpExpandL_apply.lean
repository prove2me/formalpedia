-- Prove2me | Theorems.Thm_QECCertificates_lpExpandL_apply
-- name    : QECCertificates.lpExpandL_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:42.013618+00:00
-- url     : https://prove2.me/theorems/89b07089-3f89-4411-8cc1-68be6d823ef9
-- title:
--   QECCertificates: lp Expand L apply
-- statement:
--   The QECCertificates construction uses the lp Expand L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L190-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L190-L192

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpExpandL_apply {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (s : Fin mB) (σ : G) (t : Fin nB) (τ : G) :
    lpExpandL B (s, σ) (t, τ) = rightMulMat (B s t) σ τ := by sorry
