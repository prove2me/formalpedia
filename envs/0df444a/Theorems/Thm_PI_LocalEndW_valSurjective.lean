-- Prove2me | Theorems.Thm_PI_LocalEndW_valSurjective
-- name    : PI.LocalEndW.valSurjective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:21.473701+00:00
-- url     : https://prove2.me/theorems/c3e7c2f1-1d9c-4575-8d53-c0c939dd8637
-- title:
--   Local End W: val Surjective
-- statement:
--   The Local End W construction uses the val Surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/AlgebraMapMemRange.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/AlgebraMapMemRange.lean#L39-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_AlgebraMapMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open PI PI.LocalEndW

theorem PI.LocalEndW.valSurjective : ValSurjective := by sorry
