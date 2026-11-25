-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_phAt_X
-- name    : PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_phAt_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:13.246217+00:00
-- url     : https://prove2.me/theorems/9070f1f2-b0c2-4e07-8893-844b6eb5e571
-- title:
--   Cube Relation Of Parallelogram: rename ph At X
-- statement:
--   The Cube Relation Of Parallelogram construction uses the rename ph At X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean#L159-L164

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

theorem PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_phAt_X (e : σ ↪ τ) (i : σ) :
    rename e (phAt ph (Xv (p := p) i)) = phAt ph (Xv (e i)) := by sorry
