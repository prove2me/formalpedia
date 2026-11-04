-- Prove2me | Theorems.Thm_ThreeSum_Coloring_parameter_card_log_bound
-- name    : ThreeSum.Coloring.parameter_card_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:33.092213+00:00
-- url     : https://prove2.me/theorems/0c95412b-a9fe-44a8-b661-22483b7a645e
-- title:
--   Coloring: parameter card log bound
-- statement:
--   An exact logarithmic bound, valid also for input sizes zero and one.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L126-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L126-L129

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}

theorem ThreeSum.Coloring.parameter_card_log_bound (n : ℕ) :
    Fintype.card (Parameter (indexWidth n)) ≤ 81 * (n.log2 + 1) ^ 2 := by sorry
