-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_unitaryApproxFin_of
-- name    : PI.UnitaryApproxFinWork.unitaryApproxFin_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:37.530651+00:00
-- url     : https://prove2.me/theorems/aef9d945-4a7e-4961-b562-faaea5f17716
-- title:
--   Unitary Approx Fin Work: unitary Approx Fin of
-- statement:
--   The Unitary Approx Fin Work construction uses the unitary Approx Fin of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Development.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Development.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork

theorem PI.UnitaryApproxFinWork.unitaryApproxFin_of (h1 : TopStep) (h2 : CayleyStep) (h3 : ApproxEStep)
    (hW : WeakApproxF) (hB : BddR) (hU : UnitS) (hE : EigAvoid) :
    PI.UnitaryApproxFin.UnitaryApproxFin := by sorry
