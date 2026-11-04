-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_true_original_reported
-- name    : ThreeSum.ReportingHostFrontier.true_original_reported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:58.94546+00:00
-- url     : https://prove2.me/theorems/fad9254a-b18c-4849-b25c-ea9407012b47
-- title:
--   Reporting Host Frontier: true original reported
-- statement:
--   The Reporting Host Frontier construction uses the true original reported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L92-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L92-L100

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Theorems.Thm_ThreeSum_RawReporting_true_original_reported

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostFrontier.true_original_reported {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hh : 0 < h) (hP : 0 < P) (t : Original α β γ) (ht : t ∈ T)
    (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t ∧
      word r ∈ frontier (rawOn h J P d T a b c) (wantedOf r) J := by sorry
