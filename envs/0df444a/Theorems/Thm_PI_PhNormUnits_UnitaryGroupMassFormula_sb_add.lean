-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sb_add
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.sb_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:18.713895+00:00
-- url     : https://prove2.me/theorems/6da023a4-8848-418e-977d-e50d24a827c8
-- title:
--   Unitary Group Mass Formula: sb add
-- statement:
--   The Unitary Group Mass Formula construction uses the sb add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L211-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/ConstantCoeffFormalSMul.lean#L211-L216

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.sb_add (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by sorry
