-- Prove2me | Theorems.Thm_PascalExtremes_padicVal_choose_le_of_common_suffix
-- name    : PascalExtremes.padicVal_choose_le_of_common_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:17.841576+00:00
-- url     : https://prove2.me/theorems/411e2aed-3074-4842-b0f9-e440908e686d
-- title:
--   Pascal Extremes: padic Val choose le of common suffix
-- statement:
--   If the row and selected index have the same lower `t` base-`p`
--   digits, and the remaining upper part of the row is below `p^(r+1)`,
--   then Kummer gives at most `r` carries. This is the formal counterpart of
--   the shifted leading-digit estimate used repeatedly in Stage 3.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/CarryBounds.lean#L34-L86
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/CarryBounds.lean#L34-L86

module
public import Definitions.Def_PascalExtremes_Kummer
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_CarryBounds
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.padicVal_choose_le_of_common_suffix
    {p n k u t s x r : ℕ} (hp : p.Prime)
    (hnpos : 0 < n) (hkn : k ≤ n)
    (hu : u < p ^ t)
    (hn : n = u + p ^ t * s)
    (hk : k = u + p ^ t * x)
    (hxs : x ≤ s)
    (hs : s < p ^ (r + 1)) :
    padicValNat p (n.choose k) ≤ r := by sorry
