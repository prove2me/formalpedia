-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_integrable_SB
-- name    : PositivityTheory.ThKG.Std.integrable_SB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:07:25.633466+00:00
-- url     : https://prove2.me/theorems/a279580d-30e6-4069-8ae8-6e59a01f92a6
-- title:
--   Std: integrable SB
-- statement:
--   The Std construction uses the integrable SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean#L96-L99

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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]

theorem PositivityTheory.ThKG.Std.integrable_SB {m : Measure k} (hm : IsVol m) {Φ : (κ → k) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (κ → k)) :
    Integrable Φ (Measure.pi fun _ : κ => m) := by sorry
