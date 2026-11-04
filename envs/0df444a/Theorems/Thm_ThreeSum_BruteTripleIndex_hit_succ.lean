-- Prove2me | Theorems.Thm_ThreeSum_BruteTripleIndex_hit_succ
-- name    : ThreeSum.BruteTripleIndex.hit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:35.431116+00:00
-- url     : https://prove2.me/theorems/ff36e934-fc12-4568-a609-d2f9f6fefb5b
-- title:
--   Brute Triple Index: hit succ
-- statement:
--   The Brute Triple Index construction uses the hit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BruteTripleIndex.lean#L61-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BruteTripleIndex.lean#L61-L71

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex

theorem ThreeSum.BruteTripleIndex.hit_succ {n t : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (ht : t < n^3) :
    Hit x hn (t+1) ↔ Hit x hn t ∨ witness x hn ht := by sorry
