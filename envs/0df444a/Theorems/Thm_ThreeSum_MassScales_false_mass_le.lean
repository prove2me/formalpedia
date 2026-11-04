-- Prove2me | Theorems.Thm_ThreeSum_MassScales_false_mass_le
-- name    : ThreeSum.MassScales.false_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:03.453222+00:00
-- url     : https://prove2.me/theorems/2dc967b8-50ee-406a-81fa-8405a84a2639
-- title:
--   Mass Scales: false mass le
-- statement:
--   The Mass Scales construction uses the false mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L215-L229
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L215-L229

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.MassScales.false_mass_le {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    (H : ℝ) ≤ falseMajorant k n := by sorry
