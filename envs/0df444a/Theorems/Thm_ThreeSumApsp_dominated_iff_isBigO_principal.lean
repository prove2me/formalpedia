-- Prove2me | Theorems.Thm_ThreeSumApsp_dominated_iff_isBigO_principal
-- name    : ThreeSumApsp.dominated_iff_isBigO_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:00.318394+00:00
-- url     : https://prove2.me/theorems/7441ca33-1092-4a14-a81f-c616bdbc51df
-- title:
--   Three Sum Apsp: dominated iff is Big O principal
-- statement:
--   For nonnegative functions, `Dominated` is Mathlib's big-O along the principal filter of the
--   domain.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L96-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L96-L102

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

theorem ThreeSumApsp.dominated_iff_isBigO_principal (hf : ∀ x, dom x → 0 ≤ f x)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom f g ↔ f =O[𝓟 {x | dom x}] g := by sorry
