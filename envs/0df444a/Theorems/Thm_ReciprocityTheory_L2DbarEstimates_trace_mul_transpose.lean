-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_trace_mul_transpose
-- name    : ReciprocityTheory.L2DbarEstimates.trace_mul_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:02.465832+00:00
-- url     : https://prove2.me/theorems/793efb5a-6d4f-4fca-854a-d1c2a5a9175d
-- title:
--   L2 Dbar Estimates: trace mul transpose
-- statement:
--   The L2 Dbar Estimates construction uses the trace mul transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L124-L126

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

theorem ReciprocityTheory.L2DbarEstimates.trace_mul_transpose {n : ℕ} (A V : Matrix (Fin p) (Fin n) ℂ) :
    trace (A * Vᵀ) = ∑ i, ∑ k, A i k * V i k := by sorry
