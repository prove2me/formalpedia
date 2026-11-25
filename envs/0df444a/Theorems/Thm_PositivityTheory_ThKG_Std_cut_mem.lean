-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_cut_mem
-- name    : PositivityTheory.ThKG.Std.cut_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:05:24.313847+00:00
-- url     : https://prove2.me/theorems/eff2784b-1264-4756-a21a-23e067b355b5
-- title:
--   Std: cut mem
-- statement:
--   The Std construction uses the cut mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean#L72-L88

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]

theorem PositivityTheory.ThKG.Std.cut_mem {P : Finset κ} {Φ : (κ → k) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (κ → k)) :
    (fun Z => Φ (cut P Z) * wt P Z) ∈ GlobalTheory.WeilM.SB (κ → k) := by sorry
