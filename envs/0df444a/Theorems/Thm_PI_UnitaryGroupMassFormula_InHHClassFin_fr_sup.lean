-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_sup
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.fr_sup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:42:50.827926+00:00
-- url     : https://prove2.me/theorems/58d0cc81-d1f8-487a-9043-9b6f7ee67218
-- title:
--   In HHClass Fin: fr sup
-- statement:
--   The In HHClass Fin construction uses the fr sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean#L57-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean#L57-L89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.fr_sup (hS : DefiniteCompl I S) : Submodule.span I.E S ⊔ frW I S = ⊤ := by sorry
