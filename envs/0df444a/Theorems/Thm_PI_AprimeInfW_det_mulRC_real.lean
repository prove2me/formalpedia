-- Prove2me | Theorems.Thm_PI_AprimeInfW_det_mulRC_real
-- name    : PI.AprimeInfW.det_mulRC_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:06.137747+00:00
-- url     : https://prove2.me/theorems/b64076bc-77d4-4b8c-a3d8-1388176b25fb
-- title:
--   Aprime Inf W: det mul RC real
-- statement:
--   The Aprime Inf W construction uses the det mul RC real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L29-L31

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

theorem PI.AprimeInfW.det_mulRC_real (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulRC (r := r) A).restrictScalars ℝ).det = Complex.normSq A.det ^ r := by sorry
