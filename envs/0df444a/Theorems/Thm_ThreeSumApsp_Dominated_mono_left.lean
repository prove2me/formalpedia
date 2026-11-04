-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_mono_left
-- name    : ThreeSumApsp.Dominated.mono_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:53:20.684284+00:00
-- url     : https://prove2.me/theorems/e52beb79-3739-4abd-b781-8859db2206c6
-- title:
--   Dominated: mono left
-- statement:
--   The left side may be replaced by a smaller function.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L138-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L138-L139

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
set_option autoImplicit false
public section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

theorem ThreeSumApsp.Dominated.mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g := by sorry
