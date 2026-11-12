-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_claim_3_3
-- name    : ReadOnceParityBP.LowerBound.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:48.402236+00:00
-- url     : https://prove2.me/theorems/672720e9-c6ec-4593-9889-f413a5463c20
-- title:
--   Claim 3.3 — external interval recurrence (2)
-- statement:
--   Let x,y be bits on a finite ordered set of n positions and let 0≤i≤j<n with even interval length j−i+1. With E the semantic count of valid eligible local canonical matchings whose pairs all point forward, and y_i interpreted as the natural number zero or one,
--
--   $$E_{i,j}=\sum_{\substack{i+1\le k\le j\\x_i\ne x_k}} y_i E_{i+1,k-1}E_{k+1,j}.$$
--
--   Empty subintervals have value one and odd subintervals zero. This is equation (2) with independently defined counts; the source's filter, both subintervals, and coefficient are all retained.
--
--   Differences from the source:
--   - reading: ways to match an interval using external or internal sets → E counts valid eligible local canonical matchings with every arrow forward; I counts all valid eligible local cyclic canonical matchings; reason: the global-leader reading contradicts E on the full two-point interval and I on the empty interval; the local reading preserves both displayed recurrences and the exact full count
--   - encoding: intervals [i,j], including j<i → integer endpoints with subintervals [i+1,k−1] and [k+1,j]; reason: negative endpoints represent the empty interval without truncated natural subtraction
--   - generalization: intervals embedded in the even ambient cycle → any finite ambient length, while the interval remains nonempty and even; reason: the local counts depend only on the ordered interval and its input bits; embedding in an even cycle gives the source statement
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Claim 3.3, equation (2), p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_IntervalCounts

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Claim 3.3, equation (2) (p. 9): for every nonempty even interval `[i, j] ⊆ [0, n-1]`,
`Ext_{i,j} = ∑_{k ∈ [i+1, j], x_i ≠ x_k} y_i · Ext_{i+1,k-1} · Ext_{k+1,j}`. -/
theorem claim_3_3 {n : ℕ} (x y : Fin n → Bool) (i j : ℤ) (hi : 0 ≤ i) (hij : i ≤ j) (hj : j < (n : ℤ))
    (hlen : Even (j - i + 1)) :
    extCount x y i j =
      ∑ k ∈ (Finset.Icc (i + 1) j).filter (fun k => bitAt x i ≠ bitAt x k),
        bitNat y i * extCount x y (i + 1) (k - 1) * extCount x y (k + 1) j := by sorry

end ReadOnceParityBP.LowerBound
