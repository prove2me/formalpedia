-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_comm_pow
-- name    : PositivityTheory.Rg.Rs.SliceClasses.C_comm_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:31.585266+00:00
-- url     : https://prove2.me/theorems/86760bd6-8bc5-4c41-9f3f-ab6c6083a871
-- title:
--   Slice Classes: C comm pow
-- statement:
--   The Slice Classes construction uses the C comm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/PSliceC.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/PSliceC.lean#L22-L25

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

theorem PositivityTheory.Rg.Rs.SliceClasses.C_comm_pow {M : ι → Module.End ℂ U} (hc : ∀ i j, Commute (M i) (M j)) (i j : ι) (k : ℕ) (x : U) :
    M j (((M i - 1) ^ k) x) = ((M i - 1) ^ k) (M j x) := by sorry
