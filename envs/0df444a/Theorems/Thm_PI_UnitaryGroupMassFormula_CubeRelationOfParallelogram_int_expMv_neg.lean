-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_expMv_neg
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:20.539773+00:00
-- url     : https://prove2.me/theorems/5d63a056-5fa6-47cb-ac14-162df46b7d9f
-- title:
--   Cube Relation Of Parallelogram: int exp Mv neg
-- statement:
--   The Cube Relation Of Parallelogram construction uses the int exp Mv neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L166-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L166-L192

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg {D : MvPowerSeries σ ℂ_[p]} (hD : constantCoeff D = 0)
    (h : IntegralMv (expMv D)) : IntegralMv (expMv (-D)) := by sorry
