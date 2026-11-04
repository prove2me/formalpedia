-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_isBigO
-- name    : ThreeSumApsp.Dominated.isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:14.954656+00:00
-- url     : https://prove2.me/theorems/57a50cb5-2ec1-49f4-bb2a-eea7293aa184
-- title:
--   Dominated: is Big O
-- statement:
--   A bound on `|f|` from some point on is Mathlib's `f =O[atTop] g`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L280-L285
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L280-L285

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

theorem ThreeSumApsp.Dominated.isBigO {f g : ℕ → ℝ} {n₀ : ℕ} (hfg : Dominated (fun n => n₀ ≤ n) (fun n => |f n|) g) :
    f =O[atTop] g := by sorry
