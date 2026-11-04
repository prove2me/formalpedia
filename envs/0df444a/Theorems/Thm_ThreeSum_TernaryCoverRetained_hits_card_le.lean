-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRetained_hits_card_le
-- name    : ThreeSum.TernaryCoverRetained.hits_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:00.468073+00:00
-- url     : https://prove2.me/theorems/bc360762-265a-48ab-b92a-87f3b64d02e5
-- title:
--   Ternary Cover Retained: hits card le
-- statement:
--   Inject actual edges into the product of the two actual endpoint buckets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean#L30-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean#L30-L46

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

theorem ThreeSum.TernaryCoverRetained.hits_card_le (left : E → A) (right : E → B)
    (hashL : A → K) (hashR : B → K) (VL : Finset A) (VR : Finset B)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hleft : ∀ e, left e ∈ VL) (hright : ∀ e, right e ∈ VR) (a b : K) :
    (hits left right hashL hashR a b).card ≤
      (bucket VL hashL a).card * (bucket VR hashR b).card := by sorry
