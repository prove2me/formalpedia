-- Prove2me | Theorems.Thm_PI_LocalEndW_intOfHensel
-- name    : PI.LocalEndW.intOfHensel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:45.829129+00:00
-- url     : https://prove2.me/theorems/1df8c1f0-55b5-5511-b91d-ffec672fc726
-- title:
--   Local End W: int Of Hensel
-- statement:
--   The Local End W construction uses the int Of Hensel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L74-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW

theorem PI.LocalEndW.intOfHensel : IntOfHensel := by sorry
