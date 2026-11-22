-- Prove2me | Theorems.Thm_QECCertificates_lpHX_liftConst_inl
-- name    : QECCertificates.lpHX_liftConst_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:17.78796+00:00
-- url     : https://prove2.me/theorems/e01398b0-7c20-4d8c-b6bd-c2b9dceb0cac
-- title:
--   QECCertificates: lp HX lift Const inl
-- statement:
--   **With constant seeds the X-type checks of LP are block diagonal in the group index, and every
--   block is an HGP** (left block).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L398-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L398-L406

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHX_liftConst_inl [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHX A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by sorry
