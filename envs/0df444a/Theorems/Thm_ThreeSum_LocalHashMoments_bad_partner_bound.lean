-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_bad_partner_bound
-- name    : ThreeSum.LocalHashMoments.bad_partner_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:13.767325+00:00
-- url     : https://prove2.me/theorems/092c6c70-d80c-4d50-bfc4-457692582711
-- title:
--   Local Hash Moments: bad partner bound
-- statement:
--   The Local Hash Moments construction uses the bad partner bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L51-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L51-L59

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}

theorem ThreeSum.LocalHashMoments.bad_partner_bound (e : Edge L h) :
    (HashFamily.badPartners left right e).card ≤ 2 * degree L h + groupSize h := by sorry
