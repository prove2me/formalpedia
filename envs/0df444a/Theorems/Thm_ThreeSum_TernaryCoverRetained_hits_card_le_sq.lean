-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRetained_hits_card_le_sq
-- name    : ThreeSum.TernaryCoverRetained.hits_card_le_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:02.139033+00:00
-- url     : https://prove2.me/theorems/90247793-0da3-4ba7-859d-70828da66e98
-- title:
--   Ternary Cover Retained: hits card le sq
-- statement:
--   The Ternary Cover Retained construction uses the hits card le sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean#L48-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean#L48-L60

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

theorem ThreeSum.TernaryCoverRetained.hits_card_le_sq (left : E → A) (right : E → B)
    (hashL : A → K) (hashR : B → K) (VL : Finset A) (VR : Finset B)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hleft : ∀ e, left e ∈ VL) (hright : ∀ e, right e ∈ VR)
    (a b : K) (cap : ℕ)
    (hl : (bucket VL hashL a).card ≤ cap)
    (hr : (bucket VR hashR b).card ≤ cap) :
    (hits left right hashL hashR a b).card ≤ cap ^ 2 := by sorry
