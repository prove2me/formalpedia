-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_lc_prod
-- name    : PositivityTheory.ThKG.Std.lc_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:43.981794+00:00
-- url     : https://prove2.me/theorems/4aa0cf53-e9f7-4d09-8f8e-422d992c7949
-- title:
--   Std: lc prod
-- statement:
--   The Std construction uses the lc prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean#L41-L48

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

theorem PositivityTheory.ThKG.Std.lc_prod {X ι : Type} [TopologicalSpace X] (s : Finset ι) {f : ι → X → ℂ} (h : ∀ i ∈ s, IsLocallyConstant (f i)) :
    IsLocallyConstant fun x => ∏ i ∈ s, f i x := by sorry
