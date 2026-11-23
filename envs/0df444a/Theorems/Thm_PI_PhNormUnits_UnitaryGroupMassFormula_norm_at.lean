-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_norm_at
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.norm_at
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:15.717635+00:00
-- url     : https://prove2.me/theorems/b4384bac-a774-4d51-adac-e8c4771d7975
-- title:
--   Unitary Group Mass Formula: norm at
-- statement:
--   The Unitary Group Mass Formula construction uses the norm at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/SimeqSubst1.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/SimeqSubst1.lean#L77-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
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
variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hSub hex0 hinv

theorem PI.PhNormUnits.UnitaryGroupMassFormula.norm_at {ph : PowerSeries ℂ_[p]} (c N : ℂ_[p])
    (h : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ())))
    {τ : Type} (w : MvPowerSeries τ ℂ_[p]) (hw0 : MvPowerSeries.constantCoeff w = 0) (hw : IntegralMv w) :
    Simeq (phAt ph (mulBy l ex c w)) (MvPowerSeries.C N * phAt ph w) := by sorry
