-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_sAdd
-- name    : PI.UnitaryGroupMassFormula.PhGram.sAdd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:52.606308+00:00
-- url     : https://prove2.me/theorems/bccd2526-4b67-4c86-b286-9c2e109a893b
-- title:
--   Ph Gram: s Add
-- statement:
--   The Ph Gram construction uses the s Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L50-L52

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

theorem PI.UnitaryGroupMassFormula.PhGram.sAdd {σ : Type*} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := by sorry
