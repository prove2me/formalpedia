-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv_of_le
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:46.903744+00:00
-- url     : https://prove2.me/theorems/67705488-12ee-47af-bc04-25c57c19a4d9
-- title:
--   Cube Relation Of Parallelogram: coeff exp Mv of le
-- statement:
--   The Cube Relation Of Parallelogram construction uses the coeff exp Mv of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L82-L92

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

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 0) {α : σ →₀ ℕ}
    (N : ℕ) (hN : α.degree ≤ N) :
    coeff α (expMv F) = ∑ n ∈ Finset.range (N + 1), coeff α (F ^ n) / (n.factorial : ℂ_[p]) := by sorry
