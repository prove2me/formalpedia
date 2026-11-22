-- Prove2me | Theorems.Thm_P2M_GridHam_b1_no_path__4d6679970d5b
-- name    : P2M_GridHam_b1_no_path__4d6679970d5b
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:00.307709+00:00
-- url     : https://prove2.me/theorems/84cd92e4-7391-4add-85d5-9fec644be5db
-- title:
--   P2 M Grid Ham b1 no path  4d6679970d5b: P2 M Grid Ham b1 no path  4d6679970d5b
-- statement:
--   **Base case B1, mirrored.** Same for a start at `(1, 2)`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L520-L522
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L520-L522

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_b1_no_path__4d6679970d5b (w : ℕ) (v : Coord) (hv : 3 ≤ v.1) : ¬ HasHamPath w 3 (1, 2) v := by sorry

alias «GridHam».«b1_no_path'» := P2M_GridHam_b1_no_path__4d6679970d5b
