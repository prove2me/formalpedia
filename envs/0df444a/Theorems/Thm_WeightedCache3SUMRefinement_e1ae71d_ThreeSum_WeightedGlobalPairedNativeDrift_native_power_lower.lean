-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedNativeDrift_native_power_lower
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift.native_power_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:15:40.1662+00:00
-- url     : https://prove2.me/theorems/db83cda8-022c-4835-a3f1-5be8b3789405
-- title:
--   native_power_lower
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L18-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L18-L30

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift.native_power_lower (K M R S p : ℕ) (hS : M≤S^K)
    (hp : M*R*S^2≤p^2) :
    M^(K+2)*R^K≤p^(2*K) := by sorry
