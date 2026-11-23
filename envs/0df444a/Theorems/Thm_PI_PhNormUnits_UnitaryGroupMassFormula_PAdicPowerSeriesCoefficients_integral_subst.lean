-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_integral_subst
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.integral_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:33.421259+00:00
-- url     : https://prove2.me/theorems/b0d356c2-dee3-42d8-9041-22a9210717a2
-- title:
--   PAdic Power Series Coefficients: integral subst
-- statement:
--   The PAdic Power Series Coefficients construction uses the integral subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L61-L74

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.integral_subst {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p])
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (haI : ∀ i, IntegralMv (a i))
    {f : MvPowerSeries σ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst a f) := by sorry
