-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normSq_sum_mul_le
-- name    : ReciprocityTheory.L2DbarEstimates.normSq_sum_mul_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:07.600852+00:00
-- url     : https://prove2.me/theorems/d0579fac-ef06-4618-9a2b-8b2921e5889c
-- title:
--   L2 Dbar Estimates: norm Sq sum mul le
-- statement:
--   The L2 Dbar Estimates construction uses the norm Sq sum mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L115-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.normSq_sum_mul_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    Complex.normSq (∑ q ∈ s, a q * b q) ≤
      (∑ q ∈ s, Complex.normSq (a q)) * ∑ q ∈ s, Complex.normSq (b q) := by sorry
