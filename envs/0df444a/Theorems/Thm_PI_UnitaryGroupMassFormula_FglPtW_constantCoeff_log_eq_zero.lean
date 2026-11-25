-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FglPtW_constantCoeff_log_eq_zero
-- name    : PI.UnitaryGroupMassFormula.FglPtW.constantCoeff_log_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:33.293329+00:00
-- url     : https://prove2.me/theorems/e3870b12-5593-4f13-ab06-d3e3198d0882
-- title:
--   Fgl Pt W: constant Coeff log eq zero
-- statement:
--   The Fgl Pt W construction uses the constant Coeff log eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffLogEqZero.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffLogEqZero.lean#L9-L22

import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffLogEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FglPtW
open PI.FglPtW

theorem PI.UnitaryGroupMassFormula.FglPtW.constantCoeff_log_eq_zero {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by sorry
