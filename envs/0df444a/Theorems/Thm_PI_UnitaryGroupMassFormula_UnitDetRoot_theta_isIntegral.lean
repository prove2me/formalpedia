-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_isIntegral
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.theta_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:50.466968+00:00
-- url     : https://prove2.me/theorems/01a2733f-619d-4a94-8005-27bcfe841ee9
-- title:
--   Unit Det Root: theta is Integral
-- statement:
--   The Unit Det Root construction uses the theta is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NormLeOneOfRoot.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NormLeOneOfRoot.lean#L70-L75

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.theta_isIntegral {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : IsIntegral ℚ (UnitDetRootDefs.cmTheta b d) := by sorry
