-- Prove2me | Theorems.Thm_PI_AprimeInfW_mulLC_apply
-- name    : PI.AprimeInfW.mulLC_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:07.991281+00:00
-- url     : https://prove2.me/theorems/b94442cd-6179-5efc-ae50-7438f9c2dc47
-- title:
--   Aprime Inf W: mul LC apply
-- statement:
--   The Aprime Inf W construction uses the mul LC apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L82-L85

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

theorem PI.AprimeInfW.mulLC_apply {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → Fin c → ℂ) :
    mulLC A Y = (A * Matrix.of Y : Matrix (Fin m) (Fin c) ℂ) := by sorry
