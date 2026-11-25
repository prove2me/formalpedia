-- Prove2me | Theorems.Thm_P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9
-- name    : P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:02.810133+00:00
-- url     : https://prove2.me/theorems/fe650d77-0ff2-45f7-9728-4af26bab8e02
-- title:
--   P2 M PI Biadd Of Cube Work add assoc  f28fec791de9: P2 M PI Biadd Of Cube Work add assoc  f28fec791de9
-- statement:
--   The P2 M PI Biadd Of Cube Work add assoc  f28fec791de9 construction uses the P2 M PI Biadd Of Cube Work add assoc  f28fec791de9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L47-L61

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

theorem P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9 {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (a b c : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (hc : MvPowerSeries.constantCoeff c = 0) :
    add l ex (add l ex a b) c = add l ex a (add l ex b c) := by sorry

alias «PI».«BiaddOfCubeWork».«add_assoc'» := P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9
