-- Prove2me | Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
-- name    : ThreeSum.WeightedSourceCountExecutionFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:38:55.23621+00:00
-- url     : https://prove2.me/theorems/ae6c4abe-a5f2-4148-8db1-fc50c4671ec4
-- title:
--   Ready: run
-- statement:
--   Dictionaries, joins, both signed source histograms, transformed banks,
--   and literal wanted counts all execute in the actual included program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountExecutionFactory.lean#L60-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountExecutionFactory.lean#L60-L99

import Definitions.Def_Submission_Weighted_CountExecutionFactory
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem ThreeSum.WeightedSourceCountExecutionFactory.Ready.run {N : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {leftWeight rightWeight : ℕ→ℤ} (H : Ready S lim d μ leftWeight rightWeight) :
    Meets lim S.program 134 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.left.base0 ∧ ∀ j<S.front.count,
        ν (S.front.dst+j)=LightWeightedWantedRows.score
          (S.F leftWeight) (S.G rightWeight) S.front.group S.front.Q j) := by sorry
