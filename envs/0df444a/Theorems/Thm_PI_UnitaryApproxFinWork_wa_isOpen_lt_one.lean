-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_wa_isOpen_lt_one
-- name    : PI.UnitaryApproxFinWork.wa_isOpen_lt_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:48.836961+00:00
-- url     : https://prove2.me/theorems/deb61143-5cc4-49e0-8943-bc7e29b3d27b
-- title:
--   Unitary Approx Fin Work: wa is Open lt one
-- statement:
--   The Unitary Approx Fin Work construction uses the wa is Open lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L12-L30

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

theorem PI.UnitaryApproxFinWork.wa_isOpen_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by sorry
