-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_isIntegral_of_mem_compo
-- name    : PI.AlgValsFin.W.isIntegral_of_mem_compo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:24.142843+00:00
-- url     : https://prove2.me/theorems/28b563b8-292d-4c16-8eb6-2270379b2a4b
-- title:
--   W: is Integral of mem compo
-- statement:
--   The W construction uses the is Integral of mem compo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/IsIntegralOfMemCompo.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/IsIntegralOfMemCompo.lean#L26-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.isIntegral_of_mem_compo {y : ℂ} (hy : y ∈ compo L) : IsIntegral ℚ y := by sorry
