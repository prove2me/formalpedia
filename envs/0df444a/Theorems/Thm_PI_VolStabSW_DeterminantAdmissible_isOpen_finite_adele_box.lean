-- Prove2me | Theorems.Thm_PI_VolStabSW_DeterminantAdmissible_isOpen_finite_adele_box
-- name    : PI.VolStabSW.DeterminantAdmissible.isOpen_finite_adele_box
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:16.449008+00:00
-- url     : https://prove2.me/theorems/8d2d6918-2750-40ad-9c1c-3ec4d15191cc
-- title:
--   Determinant Admissible: is Open finite adele box
-- statement:
--   The Determinant Admissible construction uses the is Open finite adele box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DetAdmA.lean#L128-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DetAdmA.lean#L128-L158

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F]

theorem PI.VolStabSW.DeterminantAdmissible.isOpen_finite_adele_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (ho : ∀ v, IsOpen (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsOpen {x : Af F | ∀ v, x v ∈ D v} := by sorry
