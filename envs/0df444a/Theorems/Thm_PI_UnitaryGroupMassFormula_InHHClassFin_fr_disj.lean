-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_disj
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.fr_disj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:38.430994+00:00
-- url     : https://prove2.me/theorems/44943b09-7648-4886-b2ca-80a8ceefe772
-- title:
--   In HHClass Fin: fr disj
-- statement:
--   The In HHClass Fin construction uses the fr disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean#L26-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean#L26-L48

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.fr_disj (hS : DefiniteCompl I S) : Disjoint (Submodule.span I.E S) (frW I S) := by sorry
