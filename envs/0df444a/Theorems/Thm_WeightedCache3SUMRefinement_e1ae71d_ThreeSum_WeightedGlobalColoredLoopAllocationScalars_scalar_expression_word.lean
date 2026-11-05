-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopAllocationScalars_scalar_expression_word
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocationScalars.scalar_expression_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:30:44.426314+00:00
-- url     : https://prove2.me/theorems/04b84d96-63ad-45ab-a37e-4dfb0db63bf1
-- title:
--   scalar_expression_word
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L90-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L90-L98

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocationScalars
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalColoredLoopAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalLocalParameters WeightedGlobalArenaLayout
set_option maxHeartbeats 200000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocationScalars.scalar_expression_word {lim : Limits} {depth : ℕ} (P : Profile κ)
    (n free : ℕ) (A B C : List ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ((P.m+P.F+P.p+fixedAlpha P.m 2+WeightedGlobalArenaSourceSetup.alphaRank P.m+
      TernaryCodeSemantics.address P.output.val+4^fixedLength P.m+P.p^(2*P.K)+
      9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K+P.scale+J P n+rounds P n : ℕ):ℤ)≤lim.word := by sorry
