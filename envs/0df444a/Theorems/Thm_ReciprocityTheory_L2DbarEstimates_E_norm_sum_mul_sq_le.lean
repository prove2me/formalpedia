-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_norm_sum_mul_sq_le
-- name    : ReciprocityTheory.L2DbarEstimates.E.norm_sum_mul_sq_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:08.668496+00:00
-- url     : https://prove2.me/theorems/c23acb50-cc7a-4e4e-98e0-4a6c4b347465
-- title:
--   E: norm sum mul sq le
-- statement:
--   The E construction uses the norm sum mul sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HalfSumNormSubSq.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HalfSumNormSubSq.lean#L26-L34

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

theorem ReciprocityTheory.L2DbarEstimates.E.norm_sum_mul_sq_le {n : ℕ} (a c : Fin n → ℂ) :
    ‖∑ j, a j * c j‖ ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 := by sorry
