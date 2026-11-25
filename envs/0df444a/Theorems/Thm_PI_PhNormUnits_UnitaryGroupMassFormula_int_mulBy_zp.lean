-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_int_mulBy_zp
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.int_mulBy_zp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:50.311438+00:00
-- url     : https://prove2.me/theorems/8b6281ab-84f1-479a-a669-37cb0d9735c3
-- title:
--   Unitary Group Mass Formula: int mul By zp
-- statement:
--   The Unitary Group Mass Formula construction uses the int mul By zp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L85-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffVar.lean#L85-L95

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
include hSub hex0 hinv

theorem PI.PhNormUnits.UnitaryGroupMassFormula.int_mulBy_zp (hC : CalcClosed) (hD : NatDense)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (n : ℤ_[p]) :
    IntegralMv (mulBy l ex (zc n) x) := by sorry
