-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_polynomialFactor_subpolynomial
-- name    : ThreeSum.HierarchyScales.polynomialFactor_subpolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:19.088109+00:00
-- url     : https://prove2.me/theorems/ef7cefd9-c03c-40ec-b62a-4a0273a97b52
-- title:
--   Hierarchy Scales: polynomial Factor subpolynomial
-- statement:
--   The Hierarchy Scales construction uses the polynomial Factor subpolynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L162-L164
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HierarchyScales.lean#L162-L164

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.HierarchyScales.polynomialFactor_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (polynomialFactor C n : ℝ) ≤ (n : ℝ) ^ d := by sorry
