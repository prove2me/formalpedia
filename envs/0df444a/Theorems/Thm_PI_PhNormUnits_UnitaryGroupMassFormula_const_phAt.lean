-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_const_phAt
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.const_phAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:14.749683+00:00
-- url     : https://prove2.me/theorems/526d02c4-f3e1-4ee3-825e-a2843a70069a
-- title:
--   Unitary Group Mass Formula: const ph At
-- statement:
--   The Unitary Group Mass Formula construction uses the const ph At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L19-L28

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.const_phAt {τ : Type*} (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries τ ℂ_[p])
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (phAt ph a) = PowerSeries.constantCoeff ph := by sorry
