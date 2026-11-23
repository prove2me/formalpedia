-- Prove2me | Theorems.Thm_P2M_Odd_neg_zpow__d07fa6a13b75
-- name    : P2M_Odd_neg_zpow__d07fa6a13b75
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:12:03.161387+00:00
-- url     : https://prove2.me/theorems/a81eaa28-6f72-44e4-96d7-4a2f9fa60cf1
-- title:
--   P2 M Odd neg zpow  d07fa6a13b75: P2 M Odd neg zpow  d07fa6a13b75
-- statement:
--   The P2 M Odd neg zpow  d07fa6a13b75 construction uses the P2 M Odd neg zpow  d07fa6a13b75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L16-L20
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L16-L20

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
set_option autoImplicit false
variable {α : Type*}
variable [GroupWithZero α] [HasDistribNeg α] {n : ℤ}

theorem P2M_Odd_neg_zpow__d07fa6a13b75 (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by sorry

alias «Odd».«neg_zpow₀» := P2M_Odd_neg_zpow__d07fa6a13b75
