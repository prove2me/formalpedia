-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_allQueryTerms_envelope
-- name    : ThreeSum.HierarchyScales.allQueryTerms_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:14.218924+00:00
-- url     : https://prove2.me/theorems/7df82cdf-cf62-46b3-b771-f2d0b21aacac
-- title:
--   Hierarchy Scales: all Query Terms envelope
-- statement:
--   The Hierarchy Scales construction uses the all Query Terms envelope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L81-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L81-L100

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.allQueryTerms_envelope {n : ℕ} (hmu : 0 < mu n) :
    (allQueryTerms n : ℝ) ≤
      hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by sorry
