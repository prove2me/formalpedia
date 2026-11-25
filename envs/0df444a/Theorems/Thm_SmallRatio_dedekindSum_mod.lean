-- Prove2me | Theorems.Thm_SmallRatio_dedekindSum_mod
-- name    : SmallRatio.dedekindSum_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:49.175235+00:00
-- url     : https://prove2.me/theorems/bd9f9ad5-609a-443c-81d6-b84890836563
-- title:
--   Small Ratio: dedekind Sum mod
-- statement:
--   The Small Ratio construction uses the dedekind Sum mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L24-L35
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean#L24-L35

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.dedekindSum_mod (h k : ℕ) (hk : 0 < k) : dedekindSum h k = dedekindSum (h % k) k := by sorry
