-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_C_mul
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.sb_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:25.760895+00:00
-- url     : https://prove2.me/theorems/994a2f70-3d25-4d8b-835c-ed7073083154
-- title:
--   Unitary Group Mass Formula: sb C mul
-- statement:
--   The Unitary Group Mass Formula construction uses the sb C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L204-L206

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.sb_C_mul (c : ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (MvPowerSeries.C c * F) = MvPowerSeries.C c * MvPowerSeries.subst s F := by sorry
