-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_claim_3_4
-- name    : ReadOnceParityBP.LowerBound.claim_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:49.768531+00:00
-- url     : https://prove2.me/theorems/75fbb22e-98e4-4db8-9281-71d5fc6d54a7
-- title:
--   Claim 3.4 — internal interval recurrence (3)
-- statement:
--   Let x,y be bits on n positions and let 0≤i≤j<n have even interval length. Let I count all valid eligible local canonical cyclic matchings and E the forward-only ones; interpret each y-bit as zero or one in the natural numbers. Then
--
--   $$I_{i,j}=\sum_{\substack{i+1\le k\le j\\x_i\ne x_k}}\left(y_k I_{i+1,k-1}E_{k+1,j}+y_i E_{i+1,k-1}I_{k+1,j}\right).$$
--
--   Empty subintervals have value one and odd subintervals zero. Both distinct endpoint coefficients and both placements of I are retained. The recurrence is an assertion about independent cardinalities, supplying the internal state of the exact-count theorem.
--
--   Differences from the source:
--   - reading: ways to match an interval using external or internal sets → E counts valid eligible local canonical matchings with every arrow forward; I counts all valid eligible local cyclic canonical matchings; reason: the global-leader reading contradicts E on the full two-point interval and I on the empty interval; the local reading preserves both displayed recurrences and the exact full count
--   - encoding: intervals [i,j], including j<i → integer endpoints with subintervals [i+1,k−1] and [k+1,j]; reason: negative endpoints represent the empty interval without truncated natural subtraction
--   - generalization: intervals embedded in the even ambient cycle → any finite ambient length, while the interval remains nonempty and even; reason: the local counts depend only on the ordered interval and its input bits; embedding in an even cycle gives the source statement
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Claim 3.4, equation (3), p.9, proof pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_IntervalCounts

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Claim 3.4, equation (3) (p. 9): for every nonempty even interval `[i, j] ⊆ [0, n-1]`,
`Int_{i,j} = ∑_{k ∈ [i+1, j], x_i ≠ x_k}
  (y_k · Int_{i+1,k-1} · Ext_{k+1,j} + y_i · Ext_{i+1,k-1} · Int_{k+1,j})`. -/
theorem claim_3_4 {n : ℕ} (x y : Fin n → Bool) (i j : ℤ) (hi : 0 ≤ i) (hij : i ≤ j) (hj : j < (n : ℤ))
    (hlen : Even (j - i + 1)) :
    intCount x y i j =
      ∑ k ∈ (Finset.Icc (i + 1) j).filter (fun k => bitAt x i ≠ bitAt x k),
        (bitNat y k * intCount x y (i + 1) (k - 1) * extCount x y (k + 1) j +
          bitNat y i * extCount x y (i + 1) (k - 1) * intCount x y (k + 1) j) := by sorry

end ReadOnceParityBP.LowerBound
