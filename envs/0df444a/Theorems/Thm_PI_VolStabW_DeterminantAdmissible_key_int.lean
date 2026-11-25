-- Prove2me | Theorems.Thm_PI_VolStabW_DeterminantAdmissible_key_int
-- name    : PI.VolStabW.DeterminantAdmissible.key_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:44:18.815299+00:00
-- url     : https://prove2.me/theorems/76495516-1eb1-4f7e-b46f-57013303d05e
-- title:
--   Determinant Admissible: key int
-- statement:
--   The Determinant Admissible construction uses the key int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L163-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean#L163-L199

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
  {a M : ℕ}

theorem PI.VolStabW.DeterminantAdmissible.key_int (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2)
    {D : Fin a × Fin M × Fin (Module.finrank F E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (f : C_c(Fin a × Fin M × Fin (Module.finrank F E) → Ainf F, ℝ)) :
    ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν1 =
      ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν2 := by sorry
