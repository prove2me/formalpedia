-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_of_le
-- name    : ThreeSumApsp.Dominated.of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:36.273636+00:00
-- url     : https://prove2.me/theorems/39912558-d19b-4c71-9f8f-b3dd98355b94
-- title:
--   Dominated: of le
-- statement:
--   A bound with constant one.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L80-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L80-L81

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

theorem ThreeSumApsp.Dominated.of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g := by sorry
