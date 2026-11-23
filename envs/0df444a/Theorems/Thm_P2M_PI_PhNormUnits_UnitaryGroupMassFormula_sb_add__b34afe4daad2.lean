-- Prove2me | Theorems.Thm_P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2
-- name    : P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:53.135812+00:00
-- url     : https://prove2.me/theorems/cc573baf-8b11-4269-afb7-be3e0ce31222
-- title:
--   P2 M PI Ph Norm Units Unitary Group Mass Formula sb add  b34afe4daad2: P2 M PI Ph Norm Units Unitary Group Mass Formula sb add  b34afe4daad2
-- statement:
--   The P2 M PI Ph Norm Units Unitary Group Mass Formula sb add  b34afe4daad2 construction uses the P2 M PI Ph Norm Units Unitary Group Mass Formula sb add  b34afe4daad2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L196-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L196-L198

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

theorem P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2 (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F + G) = MvPowerSeries.subst s F + MvPowerSeries.subst s G := by sorry

alias «PI».«PhNormUnits».«UnitaryGroupMassFormula».«sb_add'» := P2M_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add__b34afe4daad2
