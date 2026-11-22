-- Prove2me | Theorems.Thm_QECCertificates_lpHZ_inr
-- name    : QECCertificates.lpHZ_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:32.116397+00:00
-- url     : https://prove2.me/theorems/dac60d37-79eb-45d7-b6f1-80444d744c49
-- title:
--   QECCertificates: lp HZ inr
-- statement:
--   The QECCertificates construction uses the lp HZ inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L241-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L241-L245

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHZ_inr {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ A B x (Sum.inr y)
      = lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0) := by sorry
