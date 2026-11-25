-- Prove2me | Theorems.Thm_PI_LocalEndW_valOfInt
-- name    : PI.LocalEndW.valOfInt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:30.434819+00:00
-- url     : https://prove2.me/theorems/ee21d8ea-4640-441b-870c-2b34b63e9f67
-- title:
--   Local End W: val Of Int
-- statement:
--   The Local End W construction uses the val Of Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L89-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L89-L118

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

theorem PI.LocalEndW.valOfInt : ValOfInt := by sorry
