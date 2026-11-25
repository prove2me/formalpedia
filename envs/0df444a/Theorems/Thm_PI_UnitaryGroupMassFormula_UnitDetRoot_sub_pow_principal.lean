-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_sub_pow_principal
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.sub_pow_principal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:28.976359+00:00
-- url     : https://prove2.me/theorems/bacd3152-1efa-43d7-b35e-a44e5f272970
-- title:
--   Unit Det Root: sub pow principal
-- statement:
--   The Unit Det Root construction uses the sub pow principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L54-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean#L54-L80

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.sub_pow_principal (S : Submodule (𝓞 F) ℂ) (hS : S ≠ ⊥) (t : ℂ) (ht : t ≠ 0)
    (hle : S ≤ span (𝓞 F) {t}) :
    ∃ y : F, y ≠ 0 ∧ S ^ hF F = span (𝓞 F) {t ^ hF F * (y : ℂ)} := by sorry
