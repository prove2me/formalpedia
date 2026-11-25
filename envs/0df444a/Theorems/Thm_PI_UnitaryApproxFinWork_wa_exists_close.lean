-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_wa_exists_close
-- name    : PI.UnitaryApproxFinWork.wa_exists_close
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:04.916599+00:00
-- url     : https://prove2.me/theorems/efaa058f-0854-429e-b932-063ad67d9063
-- title:
--   Unitary Approx Fin Work: wa exists close
-- statement:
--   The Unitary Approx Fin Work construction uses the wa exists close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L39-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]

theorem PI.UnitaryApproxFinWork.wa_exists_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ b : F, Valued.v (x - algebraMap F (v.adicCompletion F) b) < 1 := by sorry
