-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_subst_psubst
-- name    : PI.UnitaryGroupMassFormula.PhGram.subst_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:11.878559+00:00
-- url     : https://prove2.me/theorems/4fc9f33d-6600-4978-9fd6-f650c20ba0da
-- title:
--   Ph Gram: subst psubst
-- statement:
--   The Ph Gram construction uses the subst psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L26-L32

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

theorem PI.UnitaryGroupMassFormula.PhGram.subst_psubst {s : τ → MvPowerSeries σ ℂ_[p]} (hs : MvPowerSeries.HasSubst s)
    {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by sorry
