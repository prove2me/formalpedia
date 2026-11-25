-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_zero
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.be_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:37.073422+00:00
-- url     : https://prove2.me/theorems/d6ce59f0-78ee-4ef9-b4cd-92a396056937
-- title:
--   Unitary Group Mass Formula: be zero
-- statement:
--   The Unitary Group Mass Formula construction uses the be zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L130-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L130-L137

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.be_zero {τ : Type*} {ph : PowerSeries ℂ_[p]} (hph : PowerSeries.constantCoeff ph = 0)
    (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) : be l ex ph z 0 = 0 := by sorry
