-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_front_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds.front_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:34:25.520554+00:00
-- url     : https://prove2.me/theorems/f23bb23a-293d-4901-a4cf-d2f8f2253b0e
-- title:
--   front_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L40-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L40-L99

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontBounds.front_bounds (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    let A := numbers maps τ cap M b K H drift scale n U r
    F^r*nb m r≤A.sourceHistogram ∧
    F^r*((N m r+1)*nb m r)≤A.bankCells ∧
    3*(entries (r := r) maps τ I).length≤A.tensorCells ∧
    4*nb m r≤A.bankCells ∧ 2*N m r+1≤A.prefixCells ∧
    3^(N m r)≤A.prefixCells ∧
    2*N m r*3^(N m r)+N m r≤A.nearMetadata ∧
    WeightedGlobalFrontendResources.eulerBound (N m r) (valueCap (r := r) maps cap I)+3≤A.nearDivision ∧
    WeightedGlobalFrontendResources.word (N m r) (nb m r) (F^r)
      (entries (r := r) maps τ I).length (3^(N m r)) (valueCap (r := r) maps cap I)≤A.frontendWord := by sorry
