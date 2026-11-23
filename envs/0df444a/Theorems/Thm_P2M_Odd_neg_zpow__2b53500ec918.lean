-- Prove2me | Theorems.Thm_P2M_Odd_neg_zpow__2b53500ec918
-- name    : P2M_Odd_neg_zpow__2b53500ec918
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:12:11.136937+00:00
-- url     : https://prove2.me/theorems/f5507fbd-3da5-44fd-9f6f-c4841c8cb0b7
-- title:
--   P2 M Odd neg zpow  2b53500ec918: P2 M Odd neg zpow  2b53500ec918
-- statement:
--   The P2 M Odd neg zpow  2b53500ec918 construction uses the P2 M Odd neg zpow  2b53500ec918 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L32-L34
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L32-L34

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
set_option autoImplicit false
variable {α : Type*}
variable [Group α] [HasDistribNeg α] {n : ℤ}

theorem P2M_Odd_neg_zpow__2b53500ec918 (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by sorry

alias «Odd».«neg_zpow'» := P2M_Odd_neg_zpow__2b53500ec918
