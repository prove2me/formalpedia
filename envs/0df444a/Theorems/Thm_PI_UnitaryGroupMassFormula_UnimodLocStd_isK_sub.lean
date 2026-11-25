-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_sub
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isK_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:40.087065+00:00
-- url     : https://prove2.me/theorems/f290a9c2-429c-5c8b-b111-eb641cc525bc
-- title:
--   Unimod Loc Std: is K sub
-- statement:
--   The Unimod Loc Std construction uses the is K sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/IsKTheta.lean#L39-L41

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isK_sub {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t - t') := by sorry
