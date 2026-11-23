-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_sSubst
-- name    : PI.UnitaryGroupMassFormula.PhGram.sSubst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:15.698335+00:00
-- url     : https://prove2.me/theorems/4076c798-97a6-4d36-bbb6-98cbdebccc00
-- title:
--   Ph Gram: s Subst
-- statement:
--   The Ph Gram construction uses the s Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L68-L72

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

theorem PI.UnitaryGroupMassFormula.PhGram.sSubst {σ τ : Type*} [Finite τ] (s : τ → MvPowerSeries σ ℂ_[p]) (hs : ∀ i, Good (s i))
    {f g : MvPowerSeries τ ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g) := by sorry
