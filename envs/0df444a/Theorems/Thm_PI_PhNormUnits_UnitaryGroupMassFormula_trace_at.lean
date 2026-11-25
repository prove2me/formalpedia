-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_trace_at
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.trace_at
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:20.854885+00:00
-- url     : https://prove2.me/theorems/b4a09e9c-8942-47ad-a83a-06285433754e
-- title:
--   Unitary Group Mass Formula: trace at
-- statement:
--   The Unitary Group Mass Formula construction uses the trace at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/TraceAt.lean#L30-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/TraceAt.lean#L30-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_StepUnitsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TraceAt
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
variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) (hZ : CalcZpScale)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
include hE hSub hC hD hZ hex0 hinv hph hIA hB

theorem PI.PhNormUnits.UnitaryGroupMassFormula.trace_at (c d : ℂ_[p]) (hc : IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hd : IntegralMv (mulBy l ex d (Xv ()) : MvPowerSeries Unit ℂ_[p])) (t : ℤ_[p]) (ht : c + d = zc t)
    (hsw : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))))
    (hU2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ())))
    (h2inv : ∃ h : ℤ_[p], 2 * zc h = 1) {τ : Type} (w : MvPowerSeries τ ℂ_[p])
    (w0 : MvPowerSeries.constantCoeff w = 0) (wI : IntegralMv w) :
    Simeq (be l ex ph w (mulBy l ex c w)) (MvPowerSeries.C (c + d) * phAt ph w) := by sorry
