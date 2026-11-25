-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_uJClassFin_of_latFin
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of_latFin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:42:33.453859+00:00
-- url     : https://prove2.me/theorems/27b2c2e3-7dfd-4b71-b34a-c4e4e738e8ca
-- title:
--   UJClass Fin: u JClass Fin of lat Fin
-- statement:
--   The UJClass Fin construction uses the u JClass Fin of lat Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/UJClassFinOfLatFin.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/UJClassFinOfLatFin.lean#L7-L8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOfLatFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin

theorem PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of_latFin (hS : SigPos) (hA : AdelBounds) (hB : LatFin) : PI.UJClassFin.UJClassFin := by sorry
