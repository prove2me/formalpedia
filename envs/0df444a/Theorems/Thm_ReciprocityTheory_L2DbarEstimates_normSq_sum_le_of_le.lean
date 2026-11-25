-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normSq_sum_le_of_le
-- name    : ReciprocityTheory.L2DbarEstimates.normSq_sum_le_of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:15.00341+00:00
-- url     : https://prove2.me/theorems/fa29b98d-de78-4414-9ce2-37fd033210fd
-- title:
--   L2 Dbar Estimates: norm Sq sum le of le
-- statement:
--   The L2 Dbar Estimates construction uses the norm Sq sum le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L67-L80

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.normSq_sum_le_of_le {m : ℕ} (a : Fin m → ℂ) (u L : Fin m → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hL : ∀ i, 0 ≤ L i) (h : ∀ i, Complex.normSq (a i) ≤ u i * L i) :
    Complex.normSq (∑ i, a i) ≤ (∑ i, u i) * ∑ i, L i := by sorry
