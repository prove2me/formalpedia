-- Prove2me | Theorems.Thm_QECCertificates_lpHX_inr
-- name    : QECCertificates.lpHX_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:25.213284+00:00
-- url     : https://prove2.me/theorems/25aa6cef-3b26-411f-a557-9b42ee3b21ff
-- title:
--   QECCertificates: lp HX inr
-- statement:
--   The QECCertificates construction uses the lp HX inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L229-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L229-L233

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHX_inr {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX A B x (Sum.inr y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2) := by sorry
