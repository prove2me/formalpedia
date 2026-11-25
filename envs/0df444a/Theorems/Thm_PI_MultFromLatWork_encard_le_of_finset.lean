-- Prove2me | Theorems.Thm_PI_MultFromLatWork_encard_le_of_finset
-- name    : PI.MultFromLatWork.encard_le_of_finset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:37.75815+00:00
-- url     : https://prove2.me/theorems/1d859c4d-b60a-440f-9e2c-1ab2505be7c7
-- title:
--   Mult From Lat Work: encard le of finset
-- statement:
--   The Mult From Lat Work construction uses the encard le of finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L116-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L116-L131

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL

theorem PI.MultFromLatWork.encard_le_of_finset {α : Type*} (T : Set α) (B : ℝ)
    (h : ∀ s : Finset α, (↑s : Set α) ⊆ T → (s.card : ℝ) ≤ B) :
    ((T.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal B := by sorry
