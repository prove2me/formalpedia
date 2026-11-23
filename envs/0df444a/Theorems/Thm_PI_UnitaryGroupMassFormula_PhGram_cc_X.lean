-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_X
-- name    : PI.UnitaryGroupMassFormula.PhGram.cc_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:40.125473+00:00
-- url     : https://prove2.me/theorems/c1edb19a-8cdc-4dcc-8127-4125cc4e132b
-- title:
--   Ph Gram: cc X
-- statement:
--   The Ph Gram construction uses the cc X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/HasSubstGood.lean#L145-L148

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

theorem PI.UnitaryGroupMassFormula.PhGram.cc_X {σ : Type*} (i : σ) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by sorry
