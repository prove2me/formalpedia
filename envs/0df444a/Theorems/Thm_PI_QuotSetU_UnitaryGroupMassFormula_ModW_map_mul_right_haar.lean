-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_map_mul_right_haar
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.ModW.map_mul_right_haar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:17.154507+00:00
-- url     : https://prove2.me/theorems/1ba56245-a5d1-4ecb-b9a0-62d2279d6cdf
-- title:
--   Mod W: map mul right haar
-- statement:
--   The Mod W construction uses the map mul right haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModCore.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModCore.lean#L14-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

theorem PI.QuotSetU.UnitaryGroupMassFormula.ModW.map_mul_right_haar (g : MG G hG) :
    (Measure.haar : Measure (MG G hG)).map (· * g) =
      Measure.modularCharacterFun g • (Measure.haar : Measure (MG G hG)) := by sorry
