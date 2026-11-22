-- Prove2me | Theorems.Thm_QECCertificates_lpHZ_liftConst_inr
-- name    : QECCertificates.lpHZ_liftConst_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:08.253287+00:00
-- url     : https://prove2.me/theorems/42e82917-ab32-4976-8fc3-953549d7004a
-- title:
--   QECCertificates: lp HZ lift Const inr
-- statement:
--   The QECCertificates construction uses the lp HZ lift Const inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L428-L436
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L428-L436

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHZ_liftConst_inr [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHZ A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by sorry
