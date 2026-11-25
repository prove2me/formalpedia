-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_norm_sum_sq_eq
-- name    : ReciprocityTheory.L2DbarEstimates.E.norm_sum_sq_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:43.510199+00:00
-- url     : https://prove2.me/theorems/b76bfe51-15d6-5237-b563-a3933c3a2ad1
-- title:
--   E: norm sum sq eq
-- statement:
--   The E construction uses the norm sum sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HalfSumNormSubSq.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HalfSumNormSubSq.lean#L36-L40

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

theorem ReciprocityTheory.L2DbarEstimates.E.norm_sum_sq_eq {n : ℕ} (a : Fin n → ℂ) :
    ‖∑ j, a j‖ ^ 2 = (∑ j, ∑ k, a j * conj (a k)).re := by sorry
