-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_schr_add
-- name    : PositivityTheory.ThK.LinAct.schr_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:02:06.342344+00:00
-- url     : https://prove2.me/theorems/7b68b42b-78e7-45ad-bce3-393776b10284
-- title:
--   Lin Act: schr add
-- statement:
--   The Lin Act construction uses the schr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L87-L89

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.ThK.LinAct.schr_add {w w' : (κ → k) × (κ → k)} (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by sorry
