-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_half_sum_norm_sub_sq
-- name    : ReciprocityTheory.L2DbarEstimates.E.half_sum_norm_sub_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:27.007234+00:00
-- url     : https://prove2.me/theorems/8cbb1d6a-42e8-449a-b26f-b93b20ce3968
-- title:
--   E: half sum norm sub sq
-- statement:
--   The E construction uses the half sum norm sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HalfSumNormSubSq.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HalfSumNormSubSq.lean#L42-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open scoped ComplexConjugate

theorem ReciprocityTheory.L2DbarEstimates.E.half_sum_norm_sub_sq {n : ℕ} (a : Fin n → Fin n → ℂ) :
    (∑ j, ∑ k, ‖a j k - a k j‖ ^ 2) / 2 =
      ∑ j, ∑ k, ‖a k j‖ ^ 2 - (∑ j, ∑ k, a k j * conj (a j k)).re := by sorry
