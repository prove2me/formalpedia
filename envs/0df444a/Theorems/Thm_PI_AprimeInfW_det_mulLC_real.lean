-- Prove2me | Theorems.Thm_PI_AprimeInfW_det_mulLC_real
-- name    : PI.AprimeInfW.det_mulLC_real
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:56.559463+00:00
-- url     : https://prove2.me/theorems/1e87fd0f-ee35-418e-b116-ced89ec3bd6c
-- title:
--   Aprime Inf W: det mul LC real
-- statement:
--   The Aprime Inf W construction uses the det mul LC real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L87-L90

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

theorem PI.AprimeInfW.det_mulLC_real {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulLC (c := c) A).restrictScalars ℝ).det = Complex.normSq A.det ^ c := by sorry
