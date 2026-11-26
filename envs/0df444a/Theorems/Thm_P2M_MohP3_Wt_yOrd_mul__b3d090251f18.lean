-- Prove2me | Theorems.Thm_P2M_MohP3_Wt_yOrd_mul__b3d090251f18
-- name    : P2M_MohP3_Wt_yOrd_mul__b3d090251f18
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:51:30.437329+00:00
-- url     : https://prove2.me/theorems/4307b200-57fd-5644-b83a-126b4f686be7
-- title:
--   P2 M Moh P3 Wt y Ord mul  b3d090251f18: P2 M Moh P3 Wt y Ord mul  b3d090251f18
-- statement:
--   The P2 M Moh P3 Wt y Ord mul  b3d090251f18 construction uses the P2 M Moh P3 Wt y Ord mul  b3d090251f18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L162-L164
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L162-L164

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

theorem P2M_MohP3_Wt_yOrd_mul__b3d090251f18 {p q : PowerSeries k} {m n r : ℕ} (hr : r ≤ m + n)
    (hp : YOrd p m) (hq : YOrd q n) : YOrd (p * q) r := by sorry

alias «MohP3».«Wt».«yOrd_mul'» := P2M_MohP3_Wt_yOrd_mul__b3d090251f18
