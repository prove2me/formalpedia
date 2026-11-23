-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_hasSubst_good
-- name    : PI.UnitaryGroupMassFormula.PhGram.hasSubst_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:19.689314+00:00
-- url     : https://prove2.me/theorems/a56a5480-b614-43f9-ab06-08c2cf8959cf
-- title:
--   Ph Gram: has Subst good
-- statement:
--   The Ph Gram construction uses the has Subst good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L150-L151

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

theorem PI.UnitaryGroupMassFormula.PhGram.hasSubst_good {σ τ : Type*} [Finite τ] {s : τ → MvPowerSeries σ ℂ_[p]} (hs : ∀ i, Good (s i)) :
    MvPowerSeries.HasSubst s := by sorry
