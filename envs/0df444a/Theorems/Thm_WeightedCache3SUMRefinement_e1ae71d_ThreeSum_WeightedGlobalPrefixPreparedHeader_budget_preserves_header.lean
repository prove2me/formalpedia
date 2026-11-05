-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixPreparedHeader_budget_preserves_header
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader.budget_preserves_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:02:55.050414+00:00
-- url     : https://prove2.me/theorems/ad9d83d3-c97d-414d-a625-7b2bcb8bcca5
-- title:
--   budget_preserves_header
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L40-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L40-L55

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader.budget_preserves_header {μ ν : ℕ→ℤ} {xs : List ℤ}
    {header seed power liveHeader s p a b scale xB xC xP tB tC tP : ℕ}
    (hs : Seg μ header xs) (hsep : header+xs.length≤seed)
    (hν : ν=LightTernaryBudgetStep.changed
      (LightWeightedGlobalPrefixPrepare.seedChanged μ seed power liveHeader s)
      (seed+41) p a b scale xB xC xP tB tC tP) : Seg ν header xs := by sorry
