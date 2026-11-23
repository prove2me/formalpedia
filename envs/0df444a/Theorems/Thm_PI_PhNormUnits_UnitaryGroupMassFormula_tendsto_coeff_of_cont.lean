-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_tendsto_coeff_of_cont
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.tendsto_coeff_of_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:26.757616+00:00
-- url     : https://prove2.me/theorems/7ca5e4cb-0969-458d-8b07-120a00c50c90
-- title:
--   Unitary Group Mass Formula: tendsto coeff of cont
-- statement:
--   The Unitary Group Mass Formula construction uses the tendsto coeff of cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/TendstoCoeffOfCont.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/TendstoCoeffOfCont.lean#L72-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology MvPowerSeries.WithPiTopology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]

theorem PI.PhNormUnits.UnitaryGroupMassFormula.tendsto_coeff_of_cont {τ : Type*} (F : ℂ_[p] → MvPowerSeries τ ℂ_[p]) (hF : Continuous F)
    {u : ℕ → ℂ_[p]} {c : ℂ_[p]} (hu : Tendsto u atTop (𝓝 c)) (e : τ →₀ ℕ) :
    Tendsto (fun k => MvPowerSeries.coeff e (F (u k))) atTop (𝓝 (MvPowerSeries.coeff e (F c))) := by sorry
