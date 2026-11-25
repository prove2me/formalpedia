-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_good_mulBy_sum
-- name    : PI.UnitaryGroupMassFormula.PhGram.ExpandW.good_mulBy_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:38.035804+00:00
-- url     : https://prove2.me/theorems/fad1dfdc-a5c5-5291-8c42-ad7aa559d675
-- title:
--   Expand W: good mul By sum
-- statement:
--   The Expand W construction uses the good mul By sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L74-L84

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

theorem PI.UnitaryGroupMassFormula.PhGram.ExpandW.good_mulBy_sum (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {ι : Type}
    {a : MvPowerSeries σ ℂ_[p]} (ha : Good a) (s : Finset ι) (e : ι → ℂ_[p])
    (he : ∀ i ∈ s, Good (mulBy l ex (e i) a)) : Good (mulBy l ex (∑ i ∈ s, e i) a) := by sorry
