-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_tendsto_coeff_pow
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.tendsto_coeff_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:06.193408+00:00
-- url     : https://prove2.me/theorems/3a97c8f9-9b88-44db-b29b-0baeca547ecd
-- title:
--   PAdic Power Series Coefficients: tendsto coeff pow
-- statement:
--   The PAdic Power Series Coefficients construction uses the tendsto coeff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L230-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L230-L236

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
variable {p : ℕ} [Fact p.Prime]

theorem PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.tendsto_coeff_pow {σ : Type*} {F : ℕ → MvPowerSeries σ ℂ_[p]} {f : MvPowerSeries σ ℂ_[p]}
    (hF : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f)))
    (n : ℕ) :
    ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k ^ n)) atTop (𝓝 (MvPowerSeries.coeff e (f ^ n))) := by sorry
