-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finite_owner_lift
-- name    : ThreeSum.BandRawA.finite_owner_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:55.872462+00:00
-- url     : https://prove2.me/theorems/96a76192-9be9-4007-89f4-bad2c370f2e9
-- title:
--   Band Raw A: finite owner lift
-- statement:
--   The Band Raw A construction uses the finite owner lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L84-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L84-L89

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finite_owner_lift {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) (ht : t ∈ ownerProduct nA nB nC g rs s) :
    ∃ u ∈ finiteOwnerProduct nA nB nC g rs s, coordinates u=t := by sorry
