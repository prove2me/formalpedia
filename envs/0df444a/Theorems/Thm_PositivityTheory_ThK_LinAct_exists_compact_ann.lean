-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_exists_compact_ann
-- name    : PositivityTheory.ThK.LinAct.exists_compact_ann
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:18.760579+00:00
-- url     : https://prove2.me/theorems/ddbfd196-0a23-4652-8324-d8efbf200c4d
-- title:
--   Lin Act: exists compact ann
-- statement:
--   The Lin Act construction uses the exists compact ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L71-L84

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
omit [Invertible (2 : k)]

theorem PositivityTheory.ThK.LinAct.exists_compact_ann (hc : Continuous ψ) (h1 : ψ ≠ 1) {U : Set (ι → k)} (hU : U ∈ 𝓝 (0 : ι → k)) :
    ∃ C : Set (ι → k), IsCompact C ∧ ∀ x, (∀ y ∈ U, ψ (x ⬝ᵥ y) = 1) → x ∈ C := by sorry
