-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters.cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:59.963197+00:00
-- url     : https://prove2.me/theorems/b5e6ea15-789e-4c85-ba9d-a1c36a1cbdee
-- title:
--   cutoff
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L75-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L75-L102

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters.cutoff {K m radix : ℕ} (hK : 0<K) (hm : 0<m) (hb : 1<radix)
    {κ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m radix κ<microAllowance K)
    (U : ℕ→ℕ) (hU : ∀n,1<n→(U n : ℝ)≤(n : ℝ)^κ) :
    ∃n0 : ℕ,∀n≥n0,
      let r := radixLength m n
      let J := paddedLength radix (U n) r
      1<n ∧ r<J ∧ 4*U n<radix^J ∧ n^2≤(outputSize m)^r ∧
      (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
      ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
        (determinantBound K radix)^8*n^(8*K+5) := by sorry
