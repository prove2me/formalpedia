-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopSetup_originals_query_time
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup.originals_query_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:10:26.432755+00:00
-- url     : https://prove2.me/theorems/af58c068-2bea-47df-a8c0-749be3a168cf
-- title:
--   originals_query_time
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L99-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L99-L108

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup.originals_query_time {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E] {I : Input} {A : Inputs}
    {seedCount featureBound tagBound positionCap : ℕ} {ell : E→ₗ[ZMod p] ZMod p}
    {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ : ℕ→ℤ}
    (H : WeightedGlobalArenaPrefixInputs.Originals I A seedCount featureBound tagBound positionCap ell seeds L R O μ)
    (t : ℕ) :
    WeightedGlobalArenaPrefixInputs.Originals {I with queryTime:=t} A seedCount featureBound tagBound positionCap ell seeds L R O μ := by sorry
