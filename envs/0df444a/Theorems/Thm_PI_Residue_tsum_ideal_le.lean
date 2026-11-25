-- Prove2me | Theorems.Thm_PI_Residue_tsum_ideal_le
-- name    : PI.Residue.tsum_ideal_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:21.522768+00:00
-- url     : https://prove2.me/theorems/d233ed36-0bea-47c1-b883-30713b0301ea
-- title:
--   Residue: tsum ideal le
-- statement:
--   The Residue construction uses the tsum ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L107-L111

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal
variable (E : Type*) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable (E)

theorem PI.Residue.tsum_ideal_le (w : ℕ →* ℝ≥0∞) :
    ∑' I : {I : Ideal (𝓞 E) // I ≠ ⊥}, w (absNorm I.1) ≤ (∑' k, w k) ^ Module.finrank ℚ E := by sorry
