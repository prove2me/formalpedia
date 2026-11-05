-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedNativeDrift_paired_native_drift
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift.paired_native_drift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:15:36.797794+00:00
-- url     : https://prove2.me/theorems/d95e7cb2-d954-4ba9-97d3-c2f8ecde1707
-- title:
--   paired_native_drift
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L32-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L32-L57

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift.paired_native_drift (K M R S p F : ℕ)
    (hS : M≤S^K) (hp : M*R*S^2≤p^2) (hF : (9*F)^4≤M) :
    (9*F*M*R^K)^4*M^(4*K+3)≤(p^(2*K))^4 := by sorry
