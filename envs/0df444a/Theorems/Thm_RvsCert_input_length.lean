-- Prove2me | Theorems.Thm_RvsCert_input_length
-- name    : RvsCert.input_length
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:41:36.963195+00:00
-- url     : https://prove2.me/theorems/e0614c46-b2e4-4b6e-a65e-1bfb145f6717
-- title:
--   Input length: $|(X,Y)| = n(2n-1)n\,w_X + 2n^2(2n-1)w_Y = O(n^3\log n)$
-- statement:
--   For every $n$, the input of the champion function has exactly
--   $$
--   n(2n-1)\cdot n\cdot w_X(n)\;+\;2n^2(2n-1)\cdot w_Y(n)
--   $$
--   bits ($n(2n-1)$ races with $n$ positions of $w_X(n)$ bits, and $2n^2$ athletes with $2n-1$ card entries of $w_Y(n)$ bits). Moreover there is a constant $A$ such that for all $n\ge1$ this number is at most
--   $$
--   A\,n^3(\log_2 n+1).
--   $$
--   This gives the bound $N=\tilde O(n^3)$ in Theorem 1.
--
--   Differences from the source:
--   - encoding: X and Y are bit strings of length O(n³ log n) → also the exact count n(2n−1)·n·wX n + 2n²(2n−1)·wY n of the chosen layout; reason: the count of the encoding fixed in the definitions; the paper gives only its order
--   - reading: O(n³ log n) → ≤ A·n³·(log₂ n + 1) for all n ≥ 1; reason: asymptotic notation over the family in n, constants chosen before n; the +1 keeps the log factor positive at n = 1
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, Formal definition, p.2

import Mathlib
import Definitions.Def_RvsCert_Idx

namespace RvsCert

/-- **Input length** (Formal definition, Section 2, p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "both X and Y
are bit strings of length O(n³ log n). X contains |R| = O(n²) lists X_{c,d} … each of which is
O(n log n) bits long"). The number of input bits is exactly
`n(2n − 1)·n·wX n + 2n²(2n − 1)·wY n` (races × positions × bits, plus athletes × card entries ×
bits), and it is `O(n³ log n)`: there is a constant `A` with `card (Idx n) ≤ A·n³·(log₂ n + 1)`
for every `n ≥ 1`.

**Formalization Note.** `O(n³ log n)` is read with `log₂ n + 1` so the bound is positive at
`n = 1`; `A` is chosen before `n`. -/
theorem input_length :
    (∀ n : ℕ, Fintype.card (Idx n) = n * (2 * n - 1) * n * wX n + 2 * n ^ 2 * (2 * n - 1) * wY n) ∧
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      (Fintype.card (Idx n) : ℝ) ≤ A * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) := by sorry

end RvsCert
