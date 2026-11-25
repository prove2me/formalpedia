-- Prove2me | Theorems.Thm_PI_VolStabW_DeterminantAdmissible_finprod_locBox
-- name    : PI.VolStabW.DeterminantAdmissible.finprod_locBox
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:02.438465+00:00
-- url     : https://prove2.me/theorems/fafb3074-d970-4ce4-839f-54dd0789f7d6
-- title:
--   Determinant Admissible: finprod loc Box
-- statement:
--   The Determinant Admissible construction uses the finprod loc Box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L116-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L116-L137

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

theorem PI.VolStabW.DeterminantAdmissible.finprod_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (W : Fin a → Fin M → Af F ⊗[F] E) :
    ∏ᶠ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      (boxS D).indicator 1 (crdH b (Af F) W) := by sorry
