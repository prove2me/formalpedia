-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceBounds_source_space
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.source_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:21:46.336663+00:00
-- url     : https://prove2.me/theorems/25afda65-c99a-428d-acc5-33c063f50cb8
-- title:
--   source_space
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L70-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L70-L93

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.source_space (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (right : Bool) (n : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n) :
    LightRadixKeys.space 0 (source (r := r) maps cap I right).xs.length r≤
      (r+1)*((sourceWidth maps cap)^r+1) ∧
    count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input≤
        n*(sourceWidth maps cap)^r ∧
    LightWantedSetup.space 0 (p^r) (source (r := r) maps cap I right).input
      (dictionary (source (r := r) maps cap I right).xs p r)
      (source (r := r) maps cap I right).NL
      (size (source (r := r) maps cap I right).xs r) (p*(p+1)^r) 0 0≤
        10+n+2*(sourceWidth maps cap)^r+4*p^r+p*(p+1)^r+2*n*(sourceWidth maps cap)^r := by sorry
