-- Prove2me | Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_expMv_add
-- name    : PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.expMv_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:29.056542+00:00
-- url     : https://prove2.me/theorems/b2bd5f04-869e-402e-bc97-ee0b311aec78
-- title:
--   PAdic Power Series Coefficients: exp Mv add
-- statement:
--   The PAdic Power Series Coefficients construction uses the exp Mv add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean#L162-L164

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

theorem PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.expMv_add {σ : Type*} {F G : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) : expMv (F + G) = expMv F * expMv G := by sorry
