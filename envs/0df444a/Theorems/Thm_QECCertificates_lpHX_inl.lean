-- Prove2me | Theorems.Thm_QECCertificates_lpHX_inl
-- name    : QECCertificates.lpHX_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:22.946868+00:00
-- url     : https://prove2.me/theorems/ac289a24-da34-4096-aabf-8738430ca21c
-- title:
--   QECCertificates: lp HX inl
-- statement:
--   The entrywise description of the four blocks (at the `rfl` level).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L223-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L223-L227

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHX_inl {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX A B x (Sum.inl y)
      = lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0) := by sorry
