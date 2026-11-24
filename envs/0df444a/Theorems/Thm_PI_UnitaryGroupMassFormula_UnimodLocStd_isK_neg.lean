-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_neg
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:10.702249+00:00
-- url     : https://prove2.me/theorems/fbb35c3d-d995-46f3-a0ee-09285023f6c3
-- title:
--   Unimod Loc Std: is K neg
-- statement:
--   The Unimod Loc Std construction uses the is K neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L32-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg {t : ℂ} (h : IsK b d t) : IsK b d (-t) := by sorry
