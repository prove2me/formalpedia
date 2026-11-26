-- Prove2me | Theorems.Thm_P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
-- name    : P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:59:30.480382+00:00
-- url     : https://prove2.me/theorems/d329230b-c561-40e0-835c-911072a00d8d
-- title:
--   P2 M Moh P3 Wt w Ord mul  c4d0f86c750f: P2 M Moh P3 Wt w Ord mul  c4d0f86c750f
-- statement:
--   The P2 M Moh P3 Wt w Ord mul  c4d0f86c750f construction uses the P2 M Moh P3 Wt w Ord mul  c4d0f86c750f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L92-L94
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L92-L94

module
public import Mathlib
public import Definitions.Def_MohP3_Order
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]

theorem P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f {F G : MvPowerSeries (Fin 3) k} {m n p : ℕ} (hp : p ≤ m + n)
    (hF : WOrd F m) (hG : WOrd G n) : WOrd (F * G) p := by sorry

alias «MohP3».«Wt».«wOrd_mul'» := P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
