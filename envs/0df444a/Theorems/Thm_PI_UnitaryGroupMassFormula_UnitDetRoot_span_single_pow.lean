-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_span_single_pow
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.span_single_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:31.422798+00:00
-- url     : https://prove2.me/theorems/1eff5c72-cbf5-48ac-9b92-fb20c6034cb6
-- title:
--   Unit Det Root: span single pow
-- statement:
--   The Unit Det Root construction uses the span single pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L22-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField nonZeroDivisors
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
variable (F : IntermediateField ℚ ℂ)

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.span_single_pow (x : ℂ) (n : ℕ) : span (𝓞 F) {x} ^ n = span (𝓞 F) {x ^ n} := by sorry
