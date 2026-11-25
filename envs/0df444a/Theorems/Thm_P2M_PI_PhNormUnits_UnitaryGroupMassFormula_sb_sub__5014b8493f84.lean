-- Prove2me | Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_sub__5014b8493f84
-- name    : P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_sub__5014b8493f84
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:56.158804+00:00
-- url     : https://prove2.me/theorems/1b381b1f-f8a9-4916-9aa8-5e625deceed2
-- title:
--   P2 M PI Ph Norm Units Unitary Group Mass Formula sb sub  5014b8493f84: P2 M PI Ph Norm Units Unitary Group Mass Formula sb sub  5014b8493f84
-- statement:
--   The P2 M PI Ph Norm Units Unitary Group Mass Formula sb sub  5014b8493f84 construction uses the P2 M PI Ph Norm Units Unitary Group Mass Formula sb sub  5014b8493f84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L200-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L200-L202

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
variable {σ τ : Type*} [Finite σ] {l ex : PowerSeries ℂ_[p]} (s : σ → MvPowerSeries τ ℂ_[p])
  (hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)
include hs

theorem P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_sub__5014b8493f84 (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F - G) = MvPowerSeries.subst s F - MvPowerSeries.subst s G := by sorry

alias «PI».«PhNormUnits».«UnitaryGroupMassFormula».«sb_sub'» := P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_sub__5014b8493f84
