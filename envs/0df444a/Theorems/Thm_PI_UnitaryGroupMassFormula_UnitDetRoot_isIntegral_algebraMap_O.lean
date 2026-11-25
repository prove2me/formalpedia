-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_isIntegral_algebraMap_O
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.isIntegral_algebraMap_O
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:08.500323+00:00
-- url     : https://prove2.me/theorems/9e10dc9e-61fa-5866-9af3-f9c6d56c6e7d
-- title:
--   Unit Det Root: is Integral algebra Map O
-- statement:
--   The Unit Det Root construction uses the is Integral algebra Map O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobTop.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobTop.lean#L10-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.isIntegral_algebraMap_O (F : IntermediateField ℚ ℂ) (o : 𝓞 F) :
    IsIntegral ℤ (algebraMap (𝓞 F) ℂ o) := by sorry
