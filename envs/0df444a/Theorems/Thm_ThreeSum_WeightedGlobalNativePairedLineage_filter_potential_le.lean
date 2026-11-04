-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePairedLineage_filter_potential_le
-- name    : ThreeSum.WeightedGlobalNativePairedLineage.filter_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:11:20.701648+00:00
-- url     : https://prove2.me/theorems/6ab7a85a-ecb3-4af6-88c6-7dc6e6ccb318
-- title:
--   Weighted Global Native Paired Lineage: filter potential le
-- statement:
--   A literal filter of a finite tuple index never increases its nonnegative
--   integer paired score. This is the trimming case of the injection theorem.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairedLineage.lean#L54-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairedLineage.lean#L54-L63

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairedLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalNativePairedLineage.filter_potential_le {P : Type*} [Fintype P] {d Λ : ℕ}
    (A : P→Matrix (Fin d) (Fin Λ) ℤ) (keep : P→Prop) [DecidablePred keep] :
    (∑ q : {q : P // keep q}, minorWeight (A q.val))≤potential A := by sorry
