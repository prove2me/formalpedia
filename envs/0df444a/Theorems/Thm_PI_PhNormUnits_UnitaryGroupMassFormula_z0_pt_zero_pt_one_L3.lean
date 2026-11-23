-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_z0_pt_zero_pt_one_L3
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.z0_pt_zero_pt_one_L3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:11.824658+00:00
-- url     : https://prove2.me/theorems/039fc08b-630d-40fb-9422-64bd5c205384
-- title:
--   Unitary Group Mass Formula: z0 pt zero pt one L3
-- statement:
--   The Unitary Group Mass Formula construction uses the z0 pt zero pt one L3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L98-L100

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.z0_pt_zero_pt_one_L3 (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst b ex) = 0 := by sorry
