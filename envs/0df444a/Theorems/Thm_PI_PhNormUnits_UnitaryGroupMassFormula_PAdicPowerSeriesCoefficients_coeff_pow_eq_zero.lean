-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_coeff_pow_eq_zero
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.coeff_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:12.013017+00:00
-- url     : https://prove2.me/theorems/66cb98b2-0bb5-4fa4-8cc0-8bf00d71396c
-- title:
--   PAdic Power Series Coefficients: coeff pow eq zero
-- statement:
--   The PAdic Power Series Coefficients construction uses the coeff pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L76-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L76-L95

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.coeff_pow_eq_zero {σ R : Type*} [CommRing R] {F : MvPowerSeries σ R}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    ∀ (d : ℕ) (α : σ →₀ ℕ), Finsupp.degree α < d → MvPowerSeries.coeff α (F ^ d) = 0 := by sorry
