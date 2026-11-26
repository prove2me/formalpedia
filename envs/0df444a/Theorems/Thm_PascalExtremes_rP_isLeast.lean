-- Prove2me | Theorems.Thm_PascalExtremes_rP_isLeast
-- name    : PascalExtremes.rP_isLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:52.54054+00:00
-- url     : https://prove2.me/theorems/424829b4-03dd-46de-876f-054eed344ea3
-- title:
--   Pascal Extremes: r P is Least
-- statement:
--   `rP p m` realizes the minimum definition used in the project notes.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L30-L34
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Powers.lean#L30-L34

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.rP_isLeast {p m : ℕ} (hp : 1 < p) (hm : m ≠ 0) :
    IsLeast {r : ℕ | 1 ≤ r ∧ m < p ^ r} (rP p m) := by sorry
