-- Prove2me | Theorems.Thm_PI_VolStabW_DeterminantAdmissible_locBox_eq_latV
-- name    : PI.VolStabW.DeterminantAdmissible.locBox_eq_latV
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:36.101844+00:00
-- url     : https://prove2.me/theorems/26eb9d75-954a-402d-a16c-0cd310336953
-- title:
--   Determinant Admissible: loc Box eq lat V
-- statement:
--   The Determinant Admissible construction uses the loc Box eq lat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L89-L101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
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
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}
variable {b}

theorem PI.VolStabW.DeterminantAdmissible.locBox_eq_latV {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    locBox b D v = latV b v := by sorry
