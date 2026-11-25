-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_neg
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.good_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:31.498935+00:00
-- url     : https://prove2.me/theorems/a3a05e90-cde1-55c9-9b3a-54a195010238
-- title:
--   Cube Relation Of Parallelogram: good neg
-- statement:
--   The Cube Relation Of Parallelogram construction uses the good neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L204-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L204-L205

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

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.good_neg {D : MvPowerSeries σ ℂ_[p]} (hD : Good D) : Good (-D) := by sorry
