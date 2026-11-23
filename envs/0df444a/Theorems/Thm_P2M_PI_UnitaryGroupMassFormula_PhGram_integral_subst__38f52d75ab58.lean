-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_PhGram_integral_subst__38f52d75ab58
-- name    : P2M_PI_UnitaryGroupMassFormula_PhGram_integral_subst__38f52d75ab58
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:21.492545+00:00
-- url     : https://prove2.me/theorems/0114a6cf-82ed-4f5c-897e-3975adbc8bb7
-- title:
--   P2 M PI Unitary Group Mass Formula Ph Gram integral subst  38f52d75ab58: P2 M PI Unitary Group Mass Formula Ph Gram integral subst  38f52d75ab58
-- statement:
--   The P2 M PI Unitary Group Mass Formula Ph Gram integral subst  38f52d75ab58 construction uses the P2 M PI Unitary Group Mass Formula Ph Gram integral subst  38f52d75ab58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/IntegralSubst.lean#L64-L66

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

theorem P2M_PI_UnitaryGroupMassFormula_PhGram_integral_subst__38f52d75ab58 {σ τ : Type*} [Finite τ] (s : τ → MvPowerSeries σ ℂ_[p]) (hs : ∀ i, Good (s i))
    {f : MvPowerSeries τ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst s f) := by sorry

alias «PI».«UnitaryGroupMassFormula».«PhGram».«integral_subst'» := P2M_PI_UnitaryGroupMassFormula_PhGram_integral_subst__38f52d75ab58
