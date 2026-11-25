-- Prove2me | Theorems.Thm_PI_AprimeInfW_det_mulRC
-- name    : PI.AprimeInfW.det_mulRC
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:35.459444+00:00
-- url     : https://prove2.me/theorems/41672de7-8797-5b88-8160-18937082723c
-- title:
--   Aprime Inf W: det mul RC
-- statement:
--   The Aprime Inf W construction uses the det mul RC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L22-L27

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

theorem PI.AprimeInfW.det_mulRC (A : Matrix (Fin m) (Fin m) ℂ) : (mulRC (r := r) A).det = A.det ^ r := by sorry
