-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:10.759805+00:00
-- url     : https://prove2.me/theorems/0c21e6f7-7e6a-45e3-a858-7ea984c5d6d8
-- title:
--   Cube Relation Of Parallelogram: coeff exp Mv
-- statement:
--   The Cube Relation Of Parallelogram construction uses the coeff exp Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean#L78-L80

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

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv F) =
      ∑ n ∈ Finset.range (α.degree + 1), coeff α (F ^ n) / (n.factorial : ℂ_[p]) := by sorry
