-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_cont_be
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.cont_be
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:35.893668+00:00
-- url     : https://prove2.me/theorems/6eeaf774-6f65-465b-9516-14e0f8812cc4
-- title:
--   Unitary Group Mass Formula: cont be
-- statement:
--   The Unitary Group Mass Formula construction uses the cont be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/TendstoCoeffOfCont.lean#L89-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/TendstoCoeffOfCont.lean#L89-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
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
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv

theorem PI.PhNormUnits.UnitaryGroupMassFormula.cont_be {τ : Type*} (ph : PowerSeries ℂ_[p]) (z y : MvPowerSeries τ ℂ_[p])
    (hz : MvPowerSeries.constantCoeff z = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => be l ex ph z (mulBy l ex c y) := by sorry
