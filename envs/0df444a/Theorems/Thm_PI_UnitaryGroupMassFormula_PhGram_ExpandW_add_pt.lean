-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_add_pt
-- name    : PI.UnitaryGroupMassFormula.PhGram.ExpandW.add_pt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:04.975168+00:00
-- url     : https://prove2.me/theorems/a4287087-a66c-4879-a25c-f9191f4f32f5
-- title:
--   Expand W: add pt
-- statement:
--   The Expand W construction uses the add pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L47-L50

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

theorem PI.UnitaryGroupMassFormula.PhGram.ExpandW.add_pt (hd : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (b : MvPowerSeries σ ℂ_[p]) : add l ex (pt ex x) b = pt ex (x + lg l b) := by sorry
