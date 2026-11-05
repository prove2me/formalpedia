-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedCarryBudget_initial_digit_carry_eventually
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCarryBudget.initial_digit_carry_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:29:25.39883+00:00
-- url     : https://prove2.me/theorems/d3ed3700-8835-49b6-91aa-6cb70f03e979
-- title:
--   initial_digit_carry_eventually
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedCarryBudget.lean#L16-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedCarryBudget.lean#L16-L43

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCarryBudget
open Filter Real WeightedGlobalSignedPreparationBudget WeightedGlobalSignedPadding WeightedGlobalCoverScale
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCarryBudget.initial_digit_carry_eventually {m b K : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m b κ<δ) (hδ : 4*δ<1)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      (2^(paddedLength b (U n) (radixLength m n)))^4*
        (paddedLength b (U n) (radixLength m n)+2)^(8*K)≤n := by sorry
