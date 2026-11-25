-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_exists_section
-- name    : PositivityTheory.ThK.LinAct.exists_section
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:47.478296+00:00
-- url     : https://prove2.me/theorems/6a0bd896-930b-5345-b4e5-15ad05acb638
-- title:
--   Lin Act: exists section
-- statement:
--   The Lin Act construction uses the exists section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L101-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L101-L125

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]

theorem PositivityTheory.ThK.LinAct.exists_section (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (X : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hXL : ∀ x, X x ∈ large₂ → x = 0) :
    ∃ S : (ι → k) →ₗ[k] (κ → k) × (κ → k), (∀ y, S y ∈ large₂) ∧
      ∀ x y, (X x).1 ⬝ᵥ (S y).2 - (S y).1 ⬝ᵥ (X x).2 = x ⬝ᵥ y := by sorry
