-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_hP_fst
-- name    : PI.UnitaryGroupMassFormula.PhGram.hP_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:08.620843+00:00
-- url     : https://prove2.me/theorems/96659519-50c0-4a18-8133-1fc568439619
-- title:
--   Ph Gram: h P fst
-- statement:
--   The Ph Gram construction uses the h P fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Assemble.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Assemble.lean#L25-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_PhGramOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Assemble
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

theorem PI.UnitaryGroupMassFormula.PhGram.hP_fst {κ : Type*} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) :
    (hP x y).1 = ∑ i, (x i).1 * (y i).2 := by sorry
