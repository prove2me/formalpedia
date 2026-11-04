-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_first_spec
-- name    : ThreeSum.LightPairSearch.first_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:23.803484+00:00
-- url     : https://prove2.me/theorems/689411f8-e0c2-48e5-9061-f76409ba3c6d
-- title:
--   Light Pair Search: first spec
-- statement:
--   The Light Pair Search construction uses the first spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean#L16-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean#L16-L50

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
set_option maxHeartbeats 300000

theorem ThreeSum.LightPairSearch.first_spec (good : ℕ → Prop) [DecidablePred good] : ∀ k,
    (first good k=0 ↔ ∀ i<k, ¬good i) ∧
    (∀ s, first good k=s+1 → s<k ∧ good s ∧ ∀ i<s, ¬good i) := by sorry
