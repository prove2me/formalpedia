-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_ideal_pow_principal
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.ideal_pow_principal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:27.392172+00:00
-- url     : https://prove2.me/theorems/ccc4daee-2bbb-510e-a545-cdd8de077058
-- title:
--   Unit Det Root: ideal pow principal
-- statement:
--   The Unit Det Root construction uses the ideal pow principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L40-L52

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
variable [NumberField F]

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.ideal_pow_principal (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ I ^ hF F = span (𝓞 F) {a} := by sorry
