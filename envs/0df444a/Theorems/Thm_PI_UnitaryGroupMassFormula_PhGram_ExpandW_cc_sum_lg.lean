-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_cc_sum_lg
-- name    : PI.UnitaryGroupMassFormula.PhGram.ExpandW.cc_sum_lg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:29.492838+00:00
-- url     : https://prove2.me/theorems/bc91bff7-f21d-4e8c-b8b3-6c8709531cbc
-- title:
--   Expand W: cc sum lg
-- statement:
--   The Expand W construction uses the cc sum lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L100-L104

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}

theorem PI.UnitaryGroupMassFormula.PhGram.ExpandW.cc_sum_lg (hd : Data l ex ph) {m : ℕ} {a : Fin m → MvPowerSeries σ ℂ_[p]}
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, lg l (a j)) = 0 := by sorry
