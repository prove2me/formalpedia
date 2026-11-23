-- Prove2me | Theorems.Thm_P2M_Odd_neg_one_zpow__161a9ee538a7
-- name    : P2M_Odd_neg_one_zpow__161a9ee538a7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:12:31.439716+00:00
-- url     : https://prove2.me/theorems/baa09725-fbef-43a0-acfa-ae1d8877e444
-- title:
--   P2 M Odd neg one zpow  161a9ee538a7: P2 M Odd neg one zpow  161a9ee538a7
-- statement:
--   The P2 M Odd neg one zpow  161a9ee538a7 construction uses the P2 M Odd neg one zpow  161a9ee538a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L36-L36
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean#L36-L36

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
set_option autoImplicit false
variable {α : Type*}
variable [Group α] [HasDistribNeg α] {n : ℤ}

theorem P2M_Odd_neg_one_zpow__161a9ee538a7 (h : Odd n) : (-1 : α) ^ n = -1 := by sorry

alias «Odd».«neg_one_zpow'» := P2M_Odd_neg_one_zpow__161a9ee538a7
