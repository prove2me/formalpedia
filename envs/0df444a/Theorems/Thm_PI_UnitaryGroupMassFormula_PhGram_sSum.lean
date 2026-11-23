-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_sSum
-- name    : PI.UnitaryGroupMassFormula.PhGram.sSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:31.958945+00:00
-- url     : https://prove2.me/theorems/5ef0fa40-7b04-47d3-a6d8-b669e3d6a227
-- title:
--   Ph Gram: s Sum
-- statement:
--   The Ph Gram construction uses the s Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L54-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients

theorem PI.UnitaryGroupMassFormula.PhGram.sSum {σ ι : Type*} (s : Finset ι) {f g : ι → MvPowerSeries σ ℂ_[p]} (h : ∀ i ∈ s, Simeq (f i) (g i)) :
    Simeq (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by sorry
