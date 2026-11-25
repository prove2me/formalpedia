-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_finite_of_adm
-- name    : PI.VolStabW.FiniteThetaCoordinates.finite_of_adm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:43:24.014949+00:00
-- url     : https://prove2.me/theorems/7e9f38c7-4209-400c-9167-a9ddb447b090
-- title:
--   Finite Theta Coordinates: finite of adm
-- statement:
--   The Finite Theta Coordinates construction uses the finite of adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L258-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L258-L420

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem PI.VolStabW.FiniteThetaCoordinates.finite_of_adm {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsAdm F E Φ)
    (g : GL (Fin M) (AF F ⊗[F] E)) :
    {X : Fin a → Fin M → E | Φ (actTup (AF F) g (ratTup (AF F) X)) ≠ 0}.Finite := by sorry
