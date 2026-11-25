-- Prove2me | Theorems.Thm_PI_Residue_nnreal_of_ennreal
-- name    : PI.Residue.nnreal_of_ennreal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:39.173464+00:00
-- url     : https://prove2.me/theorems/c4bf6d78-b035-4941-bc7d-008846ff1ce2
-- title:
--   Residue: nnreal of ennreal
-- statement:
--   The Residue construction uses the nnreal of ennreal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NnrealOfEnnreal.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NnrealOfEnnreal.lean#L18-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField
open scoped ENNReal NNReal

theorem PI.Residue.nnreal_of_ennreal {β : Type*} (f : β → ℝ≥0) (g : ℕ → ℝ≥0) (m : ℕ) (hg : Summable g)
    (h : ∑' b, (f b : ℝ≥0∞) ≤ (∑' k, (g k : ℝ≥0∞)) ^ m) :
    Summable f ∧ ∑' b, f b ≤ (∑' k, g k) ^ m := by sorry
