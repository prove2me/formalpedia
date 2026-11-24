-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_add
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:12.615921+00:00
-- url     : https://prove2.me/theorems/19a7f857-bd59-4356-b130-cbe5cc705abe
-- title:
--   Unimod Loc Std: is K add
-- statement:
--   The Unimod Loc Std construction uses the is K add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L24-L30

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t + t') := by sorry
