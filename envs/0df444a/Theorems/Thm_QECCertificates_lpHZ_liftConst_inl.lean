-- Prove2me | Theorems.Thm_QECCertificates_lpHZ_liftConst_inl
-- name    : QECCertificates.lpHZ_liftConst_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:14.497918+00:00
-- url     : https://prove2.me/theorems/71afceca-d165-4cc0-9c45-a29312edf36a
-- title:
--   QECCertificates: lp HZ lift Const inl
-- statement:
--   The QECCertificates construction uses the lp HZ lift Const inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L418-L426
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L418-L426

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHZ_liftConst_inl [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHZ A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by sorry
