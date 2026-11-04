-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTerminalReceipt_queries_of_record
-- name    : ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:05:19.704457+00:00
-- url     : https://prove2.me/theorems/b38de614-d27d-4617-a3b4-075cc0a13b5e
-- title:
--   Weighted Global Arena Terminal Receipt: queries of record
-- statement:
--   The last actual loop record supplies the complete bank, wanted rows and
--   live host header for the exact next selected original-prefix state.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L152-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L152-L178

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable {K : ℕ}

theorem ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_record (S : WeightedGlobalArenaLoop.Setup p m F K N E) (j : ℕ) (ω : ℕ→ℤ)
    (T : WeightedGlobalArenaLoop.LastRecord S j ω)
    (hcap : 106≤S.input.capacity) (hB : S.input.nB≤S.input.capacity)
    (hC : S.input.nC≤S.input.capacity) (hO : S.input.requesterCount≤S.input.capacity)
    (hspan : S.arrays.J*(p^j)*p≤S.input.capacity)
    (hprefix : S.input.prefixFree=addr S.input.free S.input.capacity 13)
    (hbank : S.input.prefixFree+nb m (j+1)≤addr S.input.free S.input.capacity 16)
    (hpower : S.input.prefixFree+4^(WeightedGlobalArenaSourceSetup.N m (j+1))+
      (2*WeightedGlobalArenaSourceSetup.N m (j+1)+1)≤addr S.input.free S.input.capacity 16)
    (hL : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.L i t.val)
    (hR : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.R i t.val)
    (hOraw : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.O i t.val) :
    QueryReceipt S.maps S.threshold S.cap (j+1) S.Q
      (WeightedGlobalArenaSelectedTerminal.input S.input S.arrays (S.state (j+1)) S.L S.R S.O (j+1)) ω := by sorry
