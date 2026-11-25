-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_be_nat
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.be_nat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:20.04601+00:00
-- url     : https://prove2.me/theorems/143278c8-10ec-5799-993d-3a0addd04824
-- title:
--   Unitary Group Mass Formula: be nat
-- statement:
--   The Unitary Group Mass Formula construction uses the be nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L179-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L179-L205

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
variable {ph : PowerSeries ℂ_[p]}
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hE hSub hex0 hinv hB

theorem PI.PhNormUnits.UnitaryGroupMassFormula.be_nat (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (k : ℕ) :
    Simeq (be l ex ph z (mulBy l ex (k : ℂ_[p]) y)) (MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y) := by sorry
