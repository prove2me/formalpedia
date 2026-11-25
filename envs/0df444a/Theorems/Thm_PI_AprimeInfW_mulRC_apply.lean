-- Prove2me | Theorems.Thm_PI_AprimeInfW_mulRC_apply
-- name    : PI.AprimeInfW.mulRC_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:02.73323+00:00
-- url     : https://prove2.me/theorems/859beb79-d2a4-5330-be69-d394e1265dde
-- title:
--   Aprime Inf W: mul RC apply
-- statement:
--   The Aprime Inf W construction uses the mul RC apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L17-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_TupPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix
variable {r m : ℕ}

theorem PI.AprimeInfW.mulRC_apply (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin r → Fin m → ℂ) :
    mulRC A Y = (Matrix.of Y * A : Matrix (Fin r) (Fin m) ℂ) := by sorry
