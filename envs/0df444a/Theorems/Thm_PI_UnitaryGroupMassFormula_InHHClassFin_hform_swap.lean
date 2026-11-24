-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_swap
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.hform_swap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:51.458273+00:00
-- url     : https://prove2.me/theorems/ce9e1532-b136-401a-9367-2a772d87bafa
-- title:
--   In HHClass Fin: hform swap
-- statement:
--   The In HHClass Fin construction uses the hform swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L60-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.hform_swap (x y : Fin I.n → I.E) :
    hform (starRingEnd I.E) I.J y x = starRingEnd I.E (hform (starRingEnd I.E) I.J x y) := by sorry
