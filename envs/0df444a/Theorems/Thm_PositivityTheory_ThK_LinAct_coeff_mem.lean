-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_coeff_mem
-- name    : PositivityTheory.ThK.LinAct.coeff_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:08.799799+00:00
-- url     : https://prove2.me/theorems/2abbe472-be70-4d63-8b30-203ce6d38748
-- title:
--   Lin Act: coeff mem
-- statement:
--   The Lin Act construction uses the coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L127-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActInt.lean#L127-L150

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

theorem PositivityTheory.ThK.LinAct.coeff_mem (hc : Continuous ψ) (h1 : ψ ≠ 1) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (X S : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hX : ∀ x x', (X x).1 ⬝ᵥ (X x').2 = (X x').1 ⬝ᵥ (X x).2)
    (hS : ∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (S y) φ) = l φ)
    (hXS : ∀ x y, (X x).1 ⬝ᵥ (S y).2 - (S y).1 ⬝ᵥ (X x).2 = x ⬝ᵥ y) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    (fun x => l (schr ψ (X x) φ)) ∈ SB (ι → k) := by sorry
