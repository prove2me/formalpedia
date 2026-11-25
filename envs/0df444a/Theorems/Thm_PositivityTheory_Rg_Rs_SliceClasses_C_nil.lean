-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_nil
-- name    : PositivityTheory.Rg.Rs.SliceClasses.C_nil
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:28.499745+00:00
-- url     : https://prove2.me/theorems/77516022-1719-5249-9e6c-b3d45e2db315
-- title:
--   Slice Classes: C nil
-- statement:
--   The Slice Classes construction uses the C nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/PSliceC.lean#L27-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/PSliceC.lean#L27-L69

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}

theorem PositivityTheory.Rg.Rs.SliceClasses.C_nil (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → P ≠ ⊥ → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) v = 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by sorry
