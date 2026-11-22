-- Prove2me | Theorems.Thm_QECCertificates_lpExpandR_apply
-- name    : QECCertificates.lpExpandR_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:42.387813+00:00
-- url     : https://prove2.me/theorems/9c713bf7-7ffb-433e-879a-5e4197afe560
-- title:
--   QECCertificates: lp Expand R apply
-- statement:
--   The QECCertificates construction uses the lp Expand R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L186-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L186-L188

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpExpandR_apply {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (i : Fin mA) (σ : G) (j : Fin nA) (τ : G) :
    lpExpandR A (i, σ) (j, τ) = leftMulMat (A i j) σ τ := by sorry
