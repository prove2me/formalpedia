-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixState_transition
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState.transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:09:39.596044+00:00
-- url     : https://prove2.me/theorems/33477e4d-aeed-4198-b59d-f4b378f9667e
-- title:
--   transition
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L53-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L53-L112

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState.transition (I : Input) (A : Inputs) (j b ordinal Rb Sb : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (s : State (p := p) A)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (catalog : ℕ→ℕ→ℕ)
    (raws : List ℤ) (words maps : List ℕ) (initial μ ξ ζ ν : ℕ→ℤ)
    (hmem : Memory I A L R O j s catalog initial μ)
    (hkeep : WeightedGlobalArenaScoreScan.KeepInputs I μ ξ)
    (houtputs : LightWeightedGlobalSeedScoreFull.Outputs (config p (j+1) I A ordinal)
      (data I A j b ordinal ℓ seed s.row L R O s.rows catalog) Rb Sb raws words maps ξ)
    (hspan : SpanDone (config p (j+1) I A ordinal)
      (data I A j b ordinal ℓ seed s.row L R O s.rows catalog) (addr I.free I.capacity 8) ξ ζ)
    (hcommit : LightWeightedGlobalPrefixFinish.Committed (config p (j+1) I A ordinal)
      (p^(j+1)) (addr I.free I.capacity 8) ζ ν)
    (hcapacity : A.J*(p^j)*p≤I.capacity)
    (hL : ∀i t,0≤(p:ℤ)+L i t) (hR : ∀i t,0≤(p:ℤ)+R i t) (hO : ∀i t,0≤(p:ℤ)+O i t) :
    Memory I A L R O (j+1) (extend A ℓ j s seed) (nextCatalog A ℓ j catalog seed) initial ν := by sorry
