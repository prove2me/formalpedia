-- Prove2me | Theorems.Thm_P2M_Odd_neg_one_zpow__377cb1c9a7a0
-- name    : P2M_Odd_neg_one_zpow__377cb1c9a7a0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:15.046176+00:00
-- url     : https://prove2.me/theorems/24cbc324-f498-42ae-b2de-a7e50941608b
-- title:
--   P2 M Odd neg one zpow  377cb1c9a7a0: P2 M Odd neg one zpow  377cb1c9a7a0
-- statement:
--   The P2 M Odd neg one zpow  377cb1c9a7a0 construction uses the P2 M Odd neg one zpow  377cb1c9a7a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L22-L22
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L22-L22

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
set_option autoImplicit false
variable {α : Type*}
variable [GroupWithZero α] [HasDistribNeg α] {n : ℤ}

theorem P2M_Odd_neg_one_zpow__377cb1c9a7a0 (h : Odd n) : (-1 : α) ^ n = -1 := by sorry

alias «Odd».«neg_one_zpow₀» := P2M_Odd_neg_one_zpow__377cb1c9a7a0
