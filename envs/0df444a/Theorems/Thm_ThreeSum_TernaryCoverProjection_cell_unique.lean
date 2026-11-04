-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_cell_unique
-- name    : ThreeSum.TernaryCoverProjection.cell_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:09.744361+00:00
-- url     : https://prove2.me/theorems/042e8586-0154-45cc-8ab3-346f07893f6c
-- title:
--   Ternary Cover Projection: cell unique
-- statement:
--   Apart from the merged zero-difference cells, the difference identifies
--   each admissible ordered digit pair.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L45-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L45-L51

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.cell_unique (a b c d : Fin 3)
    (hab : a.val + b.val ≤ 2) (hcd : c.val + d.val ≤ 2)
    (heq : differenceCode a b = differenceCode c d)
    (hmark : (a = 1 ∧ b = 1) ↔ (c = 1 ∧ d = 1)) :
    a = c ∧ b = d := by sorry
