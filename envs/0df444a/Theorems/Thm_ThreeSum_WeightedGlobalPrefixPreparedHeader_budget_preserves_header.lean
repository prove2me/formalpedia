-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixPreparedHeader_budget_preserves_header
-- name    : ThreeSum.WeightedGlobalPrefixPreparedHeader.budget_preserves_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:59:49.54535+00:00
-- url     : https://prove2.me/theorems/c1c7a1ae-06f6-4f61-a0a8-6aefa933ef6f
-- title:
--   Weighted Global Prefix Prepared Header: budget preserves header
-- statement:
--   The Weighted Global Prefix Prepared Header construction uses the budget preserves header property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L40-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixPreparedHeader.lean#L40-L55

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalPrefixPreparedHeader.budget_preserves_header {μ ν : ℕ→ℤ} {xs : List ℤ}
    {header seed power liveHeader s p a b scale xB xC xP tB tC tP : ℕ}
    (hs : Seg μ header xs) (hsep : header+xs.length≤seed)
    (hν : ν=LightTernaryBudgetStep.changed
      (LightWeightedGlobalPrefixPrepare.seedChanged μ seed power liveHeader s)
      (seed+41) p a b scale xB xC xP tB tC tP) : Seg ν header xs := by sorry
