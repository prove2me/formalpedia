-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finite_lift
-- name    : ThreeSum.BandRawA.finite_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:58.680202+00:00
-- url     : https://prove2.me/theorems/d27c8e99-a11c-4f3e-a408-9aa96431d457
-- title:
--   Band Raw A: finite lift
-- statement:
--   The Band Raw A construction uses the finite lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L91-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L91-L96

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by sorry
