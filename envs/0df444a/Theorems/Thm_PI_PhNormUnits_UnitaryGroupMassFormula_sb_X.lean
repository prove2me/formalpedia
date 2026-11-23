-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_X
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.sb_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:24.475579+00:00
-- url     : https://prove2.me/theorems/1ce9b76f-2d00-4f12-a944-b1d10b3b323d
-- title:
--   Unitary Group Mass Formula: sb X
-- statement:
--   The Unitary Group Mass Formula construction uses the sb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L193-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L193-L194

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.sb_X (i : σ) : MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i := by sorry
