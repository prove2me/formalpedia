-- Prove2me | Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944
-- name    : P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:48.327161+00:00
-- url     : https://prove2.me/theorems/84b40bd3-fc6d-4a74-9e80-84caf173f728
-- title:
--   P2 M PI Ph Norm Units Unitary Group Mass Formula mul By zero  192bfb31d944: P2 M PI Ph Norm Units Unitary Group Mass Formula mul By zero  192bfb31d944
-- statement:
--   The P2 M PI Ph Norm Units Unitary Group Mass Formula mul By zero  192bfb31d944 construction uses the P2 M PI Ph Norm Units Unitary Group Mass Formula mul By zero  192bfb31d944 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L157-L159

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
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
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
variable {τ : Type*}
include hex0 hinv
omit hinv

theorem P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944 (a : MvPowerSeries τ ℂ_[p]) : mulBy l ex 0 a = 0 := by sorry

alias «PI».«PhNormUnits».«UnitaryGroupMassFormula».«mulBy_zero'» := P2M_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_zero__192bfb31d944
