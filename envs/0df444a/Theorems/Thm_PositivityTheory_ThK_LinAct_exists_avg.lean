-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_exists_avg
-- name    : PositivityTheory.ThK.LinAct.exists_avg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:14.16174+00:00
-- url     : https://prove2.me/theorems/bb57fbb7-7da5-4167-8ba2-d49ad6c96cd8
-- title:
--   Lin Act: exists avg
-- statement:
--   The Lin Act construction uses the exists avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L152-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L152-L223

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

theorem PositivityTheory.ThK.LinAct.exists_avg [DecidableEq ι] (hc : Continuous ψ) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0)
    (X : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hX : ∀ x x', (X x).1 ⬝ᵥ (X x').2 = (X x').1 ⬝ᵥ (X x).2)
    (hXL : ∀ x, X x ∈ large₂ → x = 0) :
    ∃ L : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), L φ ≠ 0) ∧
      (∀ x, ∀ φ ∈ SB (κ → k), L (schr ψ (X x) φ) = L φ) ∧
      (∀ a ∈ large₂, (∀ x, (X x).1 ⬝ᵥ a.2 = a.1 ⬝ᵥ (X x).2) → ∀ φ ∈ SB (κ → k), L (schr ψ a φ) = L φ) ∧
      ∀ (T : Module.End ℂ ((κ → k) → ℂ)) (g : GL ι k) (a : ℂ), (∀ φ ∈ SB (κ → k), T φ ∈ SB (κ → k)) →
        (∀ x, ∀ φ ∈ SB (κ → k), T (schr ψ (X x) φ) = schr ψ (X (g.val *ᵥ x)) (T φ)) →
        (∀ φ ∈ SB (κ → k), l (T φ) = a * l φ) →
        ∀ φ ∈ SB (κ → k), L (T φ) = ((distribHaarChar k (GeneralLinearGroup.det g) : ℝ) : ℂ) * a * L φ := by sorry
