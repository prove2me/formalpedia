-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_ite
-- name    : ThreeSumApsp.Dominated.ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:05.750633+00:00
-- url     : https://prove2.me/theorems/99fcbf52-2b4f-4f9f-822e-e52b1de9d924
-- title:
--   Dominated: ite
-- statement:
--   A case distinction: a bound on `f₁` where `p` holds and a bound on `f₂` where it does not, both
--   by the same nonnegative `g`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L176-L187
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L176-L187

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

theorem ThreeSumApsp.Dominated.ite {p : α → Prop} [DecidablePred p]
    (h₁ : Dominated (fun x => dom x ∧ p x) f₁ g) (h₂ : Dominated (fun x => dom x ∧ ¬p x) f₂ g)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom (fun x => if p x then f₁ x else f₂ x) g := by sorry
