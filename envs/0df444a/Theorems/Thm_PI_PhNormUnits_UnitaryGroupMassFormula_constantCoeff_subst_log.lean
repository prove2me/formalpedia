-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_constantCoeff_subst_log
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.constantCoeff_subst_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:04.547358+00:00
-- url     : https://prove2.me/theorems/2cc816c6-829c-439b-88f3-13a7d9ba27e0
-- title:
--   Unitary Group Mass Formula: constant Coeff subst log
-- statement:
--   The Unitary Group Mass Formula construction uses the constant Coeff subst log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L93-L95

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.constantCoeff_subst_log (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 := by sorry
