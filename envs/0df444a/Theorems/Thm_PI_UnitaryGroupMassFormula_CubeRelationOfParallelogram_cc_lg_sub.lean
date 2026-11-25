-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_cc_lg_sub
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cc_lg_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:16.167799+00:00
-- url     : https://prove2.me/theorems/75cca12b-34a7-5d7d-a079-6e5640326013
-- title:
--   Cube Relation Of Parallelogram: cc lg sub
-- statement:
--   The Cube Relation Of Parallelogram construction uses the cc lg sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L116-L119

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
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
include hl

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cc_lg_sub (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (lg l a - lg l b) = 0 := by sorry
