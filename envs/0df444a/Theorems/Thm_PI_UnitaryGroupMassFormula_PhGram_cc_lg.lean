-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_lg
-- name    : PI.UnitaryGroupMassFormula.PhGram.cc_lg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:49.954825+00:00
-- url     : https://prove2.me/theorems/d5e2b8d8-1ae6-410b-9401-790b12110432
-- title:
--   Ph Gram: cc lg
-- statement:
--   The Ph Gram construction uses the cc lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L54-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
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
variable {σ τ : Type*}
variable {l ex ph : PowerSeries ℂ_[p]}

theorem PI.UnitaryGroupMassFormula.PhGram.cc_lg (hD : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (lg l a) = 0 := by sorry
