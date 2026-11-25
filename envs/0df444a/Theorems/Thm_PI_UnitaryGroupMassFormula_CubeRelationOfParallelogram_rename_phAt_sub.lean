-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_phAt_sub
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_phAt_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:46.541281+00:00
-- url     : https://prove2.me/theorems/ca823aa8-a027-5510-88cc-367b18e019a8
-- title:
--   Cube Relation Of Parallelogram: rename ph At sub
-- statement:
--   The Cube Relation Of Parallelogram construction uses the rename ph At sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L139-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L139-L153

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
include hex hl

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_phAt_sub (e : σ ↪ τ) (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    rename e (phAt ph (sub l ex a b)) = phAt ph (sub l ex (rename e a) (rename e b)) := by sorry
