-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_simultaneous_representation_and_ledger
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.simultaneous_representation_and_ledger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:05:31.076834+00:00
-- url     : https://prove2.me/theorems/9ed65025-a40a-45b9-9c5e-68ac5df4b6dd
-- title:
--   simultaneous_representation_and_ledger
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFiniteLedger.lean#L109-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFiniteLedger.lean#L109-L116

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.simultaneous_representation_and_ledger (c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale 40000000000 c' d) ∧
      ∀ᶠ n : ℕ in atTop,
        ((localFactor 40000000000 c' d)^
          (radixLength (scale 40000000000 c' d) n) : ℝ) ≤
            (n : ℝ)^(1/10000000000 : ℝ) := by sorry
