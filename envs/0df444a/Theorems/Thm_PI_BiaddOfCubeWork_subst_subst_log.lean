-- Prove2me | Theorems.Thm_PI_BiaddOfCubeWork_subst_subst_log
-- name    : PI.BiaddOfCubeWork.subst_subst_log
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:16.013889+00:00
-- url     : https://prove2.me/theorems/df7cb71a-f3e7-461b-9d56-b31f72515977
-- title:
--   Biadd Of Cube Work: subst subst log
-- statement:
--   The Biadd Of Cube Work construction uses the subst subst log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L27-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BiaddOfCube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
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
open PI PI.BiaddOfCubeWork
open PI.BiaddOfCube
variable {p : ℕ} [Fact p.Prime]
variable {σ : Type*}

theorem PI.BiaddOfCubeWork.subst_subst_log {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (y : MvPowerSeries σ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by sorry
