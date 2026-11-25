-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_be
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.sb_be
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:59.836918+00:00
-- url     : https://prove2.me/theorems/b0a6586e-7c97-404b-a836-a2f7feca7420
-- title:
--   Unitary Group Mass Formula: sb be
-- statement:
--   The Unitary Group Mass Formula construction uses the sb be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L229-L235

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
variable (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv

theorem PI.PhNormUnits.UnitaryGroupMassFormula.sb_be (ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (be l ex ph a b) =
      be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by sorry
