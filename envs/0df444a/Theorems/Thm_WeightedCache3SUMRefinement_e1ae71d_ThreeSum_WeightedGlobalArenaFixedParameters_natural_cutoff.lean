-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_natural_cutoff
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters.natural_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:46.974765+00:00
-- url     : https://prove2.me/theorems/3385ec56-cbea-4e6b-b9d8-c4d2e5abc2cd
-- title:
--   natural_cutoff
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L106-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L106-L118

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters.natural_cutoff {K m radix : ℕ} (hK : 0<K) (hm : 0<m) (hb : 1<radix) (κ : ℕ)
    (hcarry : carryExponent m radix (κ : ℝ)<microAllowance K) :
    ∃n0 : ℕ,∀n≥n0,
      let r := LightWeightedGlobalDimensions.r (outputSize m) n
      let J := LightWeightedGlobalDimensions.J (outputSize m) radix n (n^κ)
      1<n ∧ r<J ∧ 4*n^κ<radix^J ∧ n^2≤(outputSize m)^r ∧
      (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
      ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
        (determinantBound K radix)^8*n^(8*K+5) := by sorry
