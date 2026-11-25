-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_restrict_pow
-- name    : PositivityTheory.Rg.Rs.SliceClasses.C_restrict_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:37.482964+00:00
-- url     : https://prove2.me/theorems/34356668-6c86-4a9e-9897-94de5e83bca7
-- title:
--   Slice Classes: C restrict pow
-- statement:
--   The Slice Classes construction uses the C restrict pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/PSliceC.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/PSliceC.lean#L71-L77

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

theorem PositivityTheory.Rg.Rs.SliceClasses.C_restrict_pow {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ (m : ℕ) (x : P), (((f.restrict hf) ^ m) x : U) = (f ^ m) (x : U) := by sorry
