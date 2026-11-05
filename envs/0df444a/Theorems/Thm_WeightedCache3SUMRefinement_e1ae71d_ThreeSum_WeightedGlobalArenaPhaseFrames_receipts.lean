-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_receipts
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames.receipts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:59.682355+00:00
-- url     : https://prove2.me/theorems/79f8fff6-0ea1-4f1c-812c-1268d09d2efd
-- title:
--   receipts
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean#L27-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean#L27-L56

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseFrames
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open WeightedGlobalArenaControllerPlan WeightedGlobalArenaScoreScan
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseFrames.receipts {I : Input} {A : Inputs} {j J n U0 a b scale K R S i : ℕ}
    {D : Family (config p (j+1) I A 0)} {μ ν ξ ω : ℕ→ℤ}
    {raws : List ℤ} {words maps : List ℕ}
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (hcap : 106≤I.capacity)
    (HP : LightWeightedGlobalPrefixStep.Prepared
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j J n U0 a b scale I
        Q) μ ν)
    (HF : Final I D K R S i (addr I.free I.capacity 8) raws words maps ν ξ)
    (HC : LightWeightedGlobalPrefixFinish.Committed (config p (j+1) I A 0) (p^j*p)
      (addr I.free I.capacity 8) ξ ω) :
    ∀x,Stable I x→ω x=μ x := by sorry
