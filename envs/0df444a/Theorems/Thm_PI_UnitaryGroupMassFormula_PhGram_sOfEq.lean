-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_sOfEq
-- name    : PI.UnitaryGroupMassFormula.PhGram.sOfEq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:46.415796+00:00
-- url     : https://prove2.me/theorems/6d425f85-415f-4a19-ba36-4dfcf9800e05
-- title:
--   Ph Gram: s Of Eq
-- statement:
--   The Ph Gram construction uses the s Of Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L40-L42

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

theorem PI.UnitaryGroupMassFormula.PhGram.sOfEq {σ : Type*} {f g : MvPowerSeries σ ℂ_[p]} (h : f = g) : Simeq f g := by sorry
