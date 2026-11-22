-- Prove2me | Theorems.Thm_QECCertificates_lpHZ_inl
-- name    : QECCertificates.lpHZ_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:31.797729+00:00
-- url     : https://prove2.me/theorems/f970bf69-6d5a-4566-a177-2eb48b221442
-- title:
--   QECCertificates: lp HZ inl
-- statement:
--   The QECCertificates construction uses the lp HZ inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L235-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L235-L239

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpHZ_inl {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ A B x (Sum.inl y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2) := by sorry
