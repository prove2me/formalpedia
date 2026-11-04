-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRetained_occurrence_card_le
-- name    : ThreeSum.TernaryCoverRetained.occurrence_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:03.509988+00:00
-- url     : https://prove2.me/theorems/f4f17374-9df4-4032-83e1-4ccebbd77113
-- title:
--   Ternary Cover Retained: occurrence card le
-- statement:
--   A finite schedule sums occurrence fibers, including repeated maps.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean#L63-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean#L63-L72

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverRetained
open Finset
open scoped BigOperators
variable {E A B K : Type*} [Fintype E]
variable [DecidableEq A] [DecidableEq B] [DecidableEq K]

theorem ThreeSum.TernaryCoverRetained.occurrence_card_le {C I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (s : Finset C) (occurrence : C → I) (cap : ℕ)
    (hcap : ∀ i : I, (s.filter fun c => occurrence c = i).card ≤ cap) :
    s.card ≤ Fintype.card I * cap := by sorry
