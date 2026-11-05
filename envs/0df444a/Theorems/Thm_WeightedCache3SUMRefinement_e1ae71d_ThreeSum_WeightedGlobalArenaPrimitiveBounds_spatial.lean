-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrimitiveBounds_spatial
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrimitiveBounds.spatial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:10.321903+00:00
-- url     : https://prove2.me/theorems/a8512844-f89d-4cad-a27e-c5ebd24c71f8
-- title:
--   spatial
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L49-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L49-L89

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrimitiveBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrimitiveBounds.spatial (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (A : Inputs) (n U : ℕ)
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    I.nB≤I.capacity ∧ I.nC≤I.capacity ∧ I.requesterCount≤I.capacity ∧
    A.J+2≤I.capacity ∧ A.J*p^(r-1)≤I.capacity ∧ p^(r-1)*p≤I.capacity ∧
    3*I.requesterCount*(F*WeightedGlobalGoodOutputCatalog.cap m p τ)^r≤I.capacity ∧
    Nat.log 2 (2*WeightedGlobalArenaSeedPrimitiveGuards.rawCap m p r+1)+2≤I.capacity := by sorry
