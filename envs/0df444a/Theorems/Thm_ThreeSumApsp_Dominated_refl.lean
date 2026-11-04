-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_refl
-- name    : ThreeSumApsp.Dominated.refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:59.152059+00:00
-- url     : https://prove2.me/theorems/507cfd95-51e9-42d2-aad2-2586d9a003b1
-- title:
--   Dominated: refl
-- statement:
--   Every function is bounded by itself.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L84-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L84-L85

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

theorem ThreeSumApsp.Dominated.refl (dom : α → Prop) (f : α → ℝ) : Dominated dom f f := by sorry
