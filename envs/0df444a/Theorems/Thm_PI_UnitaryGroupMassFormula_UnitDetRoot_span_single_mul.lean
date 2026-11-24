-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_span_single_mul
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.span_single_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:57.751516+00:00
-- url     : https://prove2.me/theorems/2e6e409f-a379-4f69-bd6a-6b7da7cf109a
-- title:
--   Unit Det Root: span single mul
-- statement:
--   The Unit Det Root construction uses the span single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L25-L26

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.span_single_mul (x y : ℂ) : span (𝓞 F) {x} * span (𝓞 F) {y} = span (𝓞 F) {x * y} := by sorry
