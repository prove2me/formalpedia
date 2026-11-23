-- Prove2me | Theorems.Thm_UpperTheory_T3_normPrimesN
-- name    : UpperTheory.T3.normPrimesN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:21.621615+00:00
-- url     : https://prove2.me/theorems/bf59c4fb-4444-433f-b28a-138c6d1c463a
-- title:
--   T3: norm Primes N
-- statement:
--   The T3 construction uses the norm Primes N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/normPrimesN.lean#L108-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/normPrimesN.lean#L108-L157

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_normPrimesN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Mem.An Filter Topology
open UpperTheory UpperTheory.T3
set_option maxHeartbeats 800000

theorem UpperTheory.T3.normPrimesN :
    ShortNorm → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d : ℕ, ModAt x eps N d → ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y →
      Y ^ ((9 : ℝ) / 10) ≤ ((normPrimes d N Y (2 * Y)).card : ℝ) := by sorry
