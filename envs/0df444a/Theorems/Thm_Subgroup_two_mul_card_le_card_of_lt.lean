-- Prove2me | Theorems.Thm_Subgroup_two_mul_card_le_card_of_lt
-- name    : Subgroup.two_mul_card_le_card_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:04.807854+00:00
-- url     : https://prove2.me/theorems/989336a0-f558-4b28-adc5-d7049bda2818
-- title:
--   Subgroup: two mul card le card of lt
-- statement:
--   The Subgroup construction uses the two mul card le card of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L64-L72
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L64-L72

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas
set_option autoImplicit false
open Nat

theorem Subgroup.two_mul_card_le_card_of_lt {α : Type*} [Group α] {H K : Subgroup α}
    [Finite K] (h : H < K) : 2 * Nat.card H ≤ Nat.card K := by sorry
