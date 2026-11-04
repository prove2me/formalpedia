-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_allPrefixBoxes_envelope
-- name    : ThreeSum.HierarchyScales.allPrefixBoxes_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:10.32867+00:00
-- url     : https://prove2.me/theorems/3d8252fa-d290-43e8-93e8-283a2f439691
-- title:
--   Hierarchy Scales: all Prefix Boxes envelope
-- statement:
--   The Hierarchy Scales construction uses the all Prefix Boxes envelope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L64-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L64-L79

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.allPrefixBoxes_envelope {n : ℕ} (hmu : 0 < mu n) :
    (allPrefixBoxes n : ℝ) ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by sorry
