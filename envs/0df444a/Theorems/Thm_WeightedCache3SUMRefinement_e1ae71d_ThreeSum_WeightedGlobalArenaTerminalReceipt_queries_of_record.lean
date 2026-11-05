-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaTerminalReceipt_queries_of_record
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:02:45.964108+00:00
-- url     : https://prove2.me/theorems/36cd6816-b3e8-4925-b59b-746363d3b5ae
-- title:
--   queries_of_record
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L152-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L152-L178

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable {K : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_record (S : WeightedGlobalArenaLoop.Setup p m F K N E) (j : ℕ) (ω : ℕ→ℤ)
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
