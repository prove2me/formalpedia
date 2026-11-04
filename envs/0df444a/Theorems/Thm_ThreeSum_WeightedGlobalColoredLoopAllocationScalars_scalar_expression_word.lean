-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocationScalars_scalar_expression_word
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocationScalars.scalar_expression_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:32:29.129626+00:00
-- url     : https://prove2.me/theorems/fba7b925-936f-43ae-8d32-676db5631c6f
-- title:
--   Weighted Global Colored Loop Allocation Scalars: scalar expression word
-- statement:
--   Exact scalar sum used by the actual initialized-loop call. Keeping
--   this arithmetic statement independent of the extension avoids re-elaborating
--   its field instances merely to bound twelve integer constants.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L90-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L90-L98

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocationScalars
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalColoredLoopAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalLocalParameters WeightedGlobalArenaLayout
set_option maxHeartbeats 200000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopAllocationScalars.scalar_expression_word {lim : Limits} {depth : ℕ} (P : Profile κ)
    (n free : ℕ) (A B C : List ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ((P.m+P.F+P.p+fixedAlpha P.m 2+WeightedGlobalArenaSourceSetup.alphaRank P.m+
      TernaryCodeSemantics.address P.output.val+4^fixedLength P.m+P.p^(2*P.K)+
      9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K+P.scale+J P n+rounds P n : ℕ):ℤ)≤lim.word := by sorry
