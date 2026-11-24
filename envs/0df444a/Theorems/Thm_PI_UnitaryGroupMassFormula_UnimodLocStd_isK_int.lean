-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_int
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:46.263799+00:00
-- url     : https://prove2.me/theorems/d33253b4-4347-42b1-8325-ce14acfd76dd
-- title:
--   Unimod Loc Std: is K int
-- statement:
--   The Unimod Loc Std construction uses the is K int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L16-L18

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (n : ℤ) : IsK b d n := by sorry
