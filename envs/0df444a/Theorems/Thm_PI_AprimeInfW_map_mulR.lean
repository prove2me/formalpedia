-- Prove2me | Theorems.Thm_PI_AprimeInfW_map_mulR
-- name    : PI.AprimeInfW.map_mulR
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:06.504581+00:00
-- url     : https://prove2.me/theorems/ba20e11b-03f0-570b-afde-dbe91ee5e9cb
-- title:
--   Aprime Inf W: map mul R
-- statement:
--   The Aprime Inf W construction uses the map mul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean#L52-L69

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

theorem PI.AprimeInfW.map_mulR (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool))).map
        (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) =
      ENNReal.ofReal (Complex.normSq A.det ^ r)⁻¹ • volume := by sorry
