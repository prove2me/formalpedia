-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_algebraMap_O_apply
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.algebraMap_O_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:16.290744+00:00
-- url     : https://prove2.me/theorems/5bdded4d-daca-4f39-8a1a-5fe5deb080e1
-- title:
--   Unit Det Root: algebra Map O apply
-- statement:
--   The Unit Det Root construction uses the algebra Map O apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L33-L34

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.algebraMap_O_apply (o : 𝓞 F) : algebraMap (𝓞 F) ℂ o = ((algebraMap (𝓞 F) F o : F) : ℂ) := by sorry
