-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_coeff_expMv
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.coeff_expMv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:30.988423+00:00
-- url     : https://prove2.me/theorems/91dcbd08-06b4-4c56-b439-9f45d3ef162c
-- title:
--   PAdic Power Series Coefficients: coeff exp Mv
-- statement:
--   The PAdic Power Series Coefficients construction uses the coeff exp Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L97-L100

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.coeff_expMv {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (expMv F) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p]) := by sorry
