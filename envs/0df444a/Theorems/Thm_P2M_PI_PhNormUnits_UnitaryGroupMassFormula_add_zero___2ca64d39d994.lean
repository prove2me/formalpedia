-- Prove2me | Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_zero___2ca64d39d994
-- name    : P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_zero___2ca64d39d994
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:57.056523+00:00
-- url     : https://prove2.me/theorems/920abce4-5b15-4584-bc8f-1aa3f55b8b2c
-- title:
--   P2 M PI Ph Norm Units Unitary Group Mass Formula add zero   2ca64d39d994: P2 M PI Ph Norm Units Unitary Group Mass Formula add zero   2ca64d39d994
-- statement:
--   The P2 M PI Ph Norm Units Unitary Group Mass Formula add zero   2ca64d39d994 construction uses the P2 M PI Ph Norm Units Unitary Group Mass Formula add zero   2ca64d39d994 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L121-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology MvPowerSeries.WithPiTopology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv

theorem P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_zero___2ca64d39d994 {τ : Type*} (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) :
    add l ex z 0 = z := by sorry

alias «PI».«PhNormUnits».«UnitaryGroupMassFormula».«add_zero''» := P2M_PI_PhNormUnits_UnitaryGroupMassFormula_add_zero___2ca64d39d994
