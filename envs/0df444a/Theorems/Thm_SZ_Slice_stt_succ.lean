-- Prove2me | Theorems.Thm_SZ_Slice_stt_succ
-- name    : SZ.Slice.stt_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:26.272458+00:00
-- url     : https://prove2.me/theorems/374eb321-a8d1-482a-a28e-d906654da0d8
-- title:
--   Slice: stt succ
-- statement:
--   The Slice construction uses the stt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L124-L126
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L124-L126

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.stt_succ (S : Slice) (j k₀ : ℤ) (k : ℕ) :
    stt S j k₀ (k + 1) = ((S.m : ℤ) * ((stt S j k₀ k).1 - S.dA (S.w0 j k₀) k),
      (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k)) := by sorry
