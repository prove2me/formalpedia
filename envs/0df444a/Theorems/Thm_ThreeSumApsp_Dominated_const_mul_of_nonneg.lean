-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_const_mul_of_nonneg
-- name    : ThreeSumApsp.Dominated.const_mul_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:57.679291+00:00
-- url     : https://prove2.me/theorems/0a7ae156-b291-4a8e-8183-01d0abeaf7ec
-- title:
--   Dominated: const mul of nonneg
-- statement:
--   A constant factor of any sign in front of a function that is nonnegative on the domain is
--   absorbed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L206-L208
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L206-L208

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

theorem ThreeSumApsp.Dominated.const_mul_of_nonneg (hfg : Dominated dom f g) (c : ℝ) (hf : ∀ x, dom x → 0 ≤ f x) :
    Dominated dom (fun x => c * f x) g := by sorry
