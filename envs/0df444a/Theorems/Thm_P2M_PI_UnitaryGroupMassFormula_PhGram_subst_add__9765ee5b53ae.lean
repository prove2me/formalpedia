-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae
-- name    : P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:41.458877+00:00
-- url     : https://prove2.me/theorems/f7507f17-74b6-45a2-aec6-71e8145569c8
-- title:
--   P2 M PI Unitary Group Mass Formula Ph Gram subst add  9765ee5b53ae: P2 M PI Unitary Group Mass Formula Ph Gram subst add  9765ee5b53ae
-- statement:
--   The P2 M PI Unitary Group Mass Formula Ph Gram subst add  9765ee5b53ae construction uses the P2 M PI Unitary Group Mass Formula Ph Gram subst add  9765ee5b53ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L107-L114

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
variable {s : τ → MvPowerSeries σ ℂ_[p]}

theorem P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) {a b : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by sorry

alias «PI».«UnitaryGroupMassFormula».«PhGram».«subst_add'» := P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae
