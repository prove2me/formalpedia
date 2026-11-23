-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ofReal_normSq_sum_mul
-- name    : ReciprocityTheory.L2DbarEstimates.ofReal_normSq_sum_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:58.380587+00:00
-- url     : https://prove2.me/theorems/67c479fb-111d-4153-b2b5-f3da1f9bd383
-- title:
--   L2 Dbar Estimates: of Real norm Sq sum mul
-- statement:
--   The L2 Dbar Estimates construction uses the of Real norm Sq sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L30-L35

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

theorem ReciprocityTheory.L2DbarEstimates.ofReal_normSq_sum_mul (a ξ : Fin n → ℂ) :
    ((Complex.normSq (∑ j, a j * ξ j) : ℝ) : ℂ) =
      ∑ j, ∑ kk, a j * conj (a kk) * ξ j * conj (ξ kk) := by sorry
