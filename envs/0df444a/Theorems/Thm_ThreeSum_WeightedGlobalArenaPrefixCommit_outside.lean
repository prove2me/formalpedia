-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixCommit_outside
-- name    : ThreeSum.WeightedGlobalArenaPrefixCommit.outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:54:25.849832+00:00
-- url     : https://prove2.me/theorems/5cca3cfc-655b-4828-b147-6d2bde44c566
-- title:
--   Weighted Global Arena Prefix Commit: outside
-- statement:
--   Committing only the retained key/span regions leaves actual banks,
--   headers, menus and original digit matrices unchanged.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean#L49-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean#L49-L52

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish

theorem ThreeSum.WeightedGlobalArenaPrefixCommit.outside {C : Config} {rows newSpan : ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν) (x : ℕ)
    (hk : x<C.Bold ∨ C.Oold+C.nO≤x) (hs : x<C.catalog ∨ C.catalog+rows*C.J≤x) :
    ν x=ξ x := by sorry
