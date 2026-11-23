-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_psubst
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:32.206293+00:00
-- url     : https://prove2.me/theorems/6ff1b94e-034b-4dad-9daa-f409a4c52079
-- title:
--   Cube Relation Of Parallelogram: rename psubst
-- statement:
--   The Cube Relation Of Parallelogram construction uses the rename psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L71-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
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
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_psubst (e : σ ↪ τ) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst a g) = PowerSeries.subst (rename e a) g := by sorry
