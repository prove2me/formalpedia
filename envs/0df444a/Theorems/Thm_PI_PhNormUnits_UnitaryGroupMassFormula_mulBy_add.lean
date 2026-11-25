-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_mulBy_add
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.mulBy_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:50.333911+00:00
-- url     : https://prove2.me/theorems/0d524011-273d-4a39-b96e-6f05f6c76505
-- title:
--   Unitary Group Mass Formula: mul By add
-- statement:
--   The Unitary Group Mass Formula construction uses the mul By add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L139-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L139-L146

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.mulBy_add (c : ℂ_[p]) (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    mulBy l ex c (add l ex a b) = add l ex (mulBy l ex c a) (mulBy l ex c b) := by sorry
