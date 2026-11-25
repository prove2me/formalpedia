-- Prove2me | Theorems.Thm_PI_VolStabW_DeterminantAdmissible_mem_upd
-- name    : PI.VolStabW.DeterminantAdmissible.mem_upd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:46:48.521078+00:00
-- url     : https://prove2.me/theorems/44cde79f-90e4-45ff-86b1-d800608a908d
-- title:
--   Determinant Admissible: mem upd
-- statement:
--   The Determinant Admissible construction uses the mem upd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmB.lean#L117-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmB.lean#L117-L150

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
open Classical

theorem PI.VolStabW.DeterminantAdmissible.mem_upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) (y : ι → Af F) :
    y ∈ boxS (upd D c v C) ↔ y ∈ boxS D ∧ y c v ∈ C := by sorry
