-- Prove2me | Theorems.Thm_RandOrderSort_remark_3_2
-- name    : RandOrderSort.remark_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:36.611275+00:00
-- url     : https://prove2.me/theorems/1ce362a3-182a-4fd9-a263-920c43c82b05
-- title:
--   Remark 3.2 — bounds used in the analysis, displays (16)–(17)
-- statement:
--   For $n\ge 8192$, every nonfinal bucket has capacity at most $1024$: growing buckets have capacity $2T$, and shrinking buckets have capacity at most $B+7\le 345$. For a nonfinal shrinking phase,
--   $$\frac{3B}{4}-1\le\frac{n_i}{b_i}\le\frac34(B+7).$$
--   Writing $b=b_1$, also
--   $$b\le N/256,\qquad \frac mb>\frac{256}{7}>32.$$
--   Finally $L\le\log_2 n$ and $k\le\log_2 n$, and at most one fresh block is appended in each phase: on every execution the allocated prefix grows only at the first arrival of a phase, and then by exactly that phase's fresh block.
--
--   These are the numerical facts used by Lemmas 4.9, 4.11 and 4.12 and Proposition 4.15.
--
--   Differences from the source:
--   - generalization: L + k = O(log n) → `L n ≤ Nat.log 2 n ∧ k n ≤ Nat.log 2 n`; reason: the explicit form the paper itself uses in the proof of Proposition 4.15 (p.37: "Since L, k ≤ log2 n"); it is a stronger conclusion that implies the O(log n) claim
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Remark 3.2, p.18, displays (16), (17)

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort

namespace RandOrderSort

/-- **Remark 3.2 (Bounds used in the analysis)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.18: "Every nonfinal bucket has capacity at
most 1024: growing buckets have capacity 2T, and shrinking buckets have capacity at most
B + 7 ≤ 345. For a nonfinal shrinking phase, 3B/4 − 1 ≤ n_i/b_i ≤ 3/4(B + 7). (16) … Writing
b = b_1, we also have b ≤ N/256, m/b > 256/7 > 32. (17) … Finally, L + k = O(log n), and at most
one fresh block is appended in each phase."

**Formalization Note.** For `n ≥ 8192`. "Nonfinal" is every phase `p` with `p + 1 < L + k`.
`L + k = O(log n)` is stated in the form the proof of Proposition 4.15 uses, `L ≤ log₂ n` and
`k ≤ log₂ n` (`Nat.log 2`). "At most one fresh block per phase": on every execution the allocated
prefix grows only at the first arrival of a phase, and then by exactly that phase's fresh block. -/
theorem remark_3_2 : ∀ n, 16 * T ≤ n →
    (∀ p, p + 1 < numPhases n → ∀ ℓ < phaseLeaves n p, phaseCap n p ℓ ≤ 1024) ∧
    (∀ j < L n, ∀ ℓ, phaseCap n j ℓ = 2 * T) ∧
    (∀ i, 1 ≤ i → i < k n → ∀ ℓ < b n i, shrinkCap n i ℓ ≤ B n + 7) ∧ B n + 7 ≤ 345 ∧
    (∀ i, 1 ≤ i → i < k n →
      3 * (B n : ℝ) / 4 - 1 ≤ (nPh n i : ℝ) / b n i ∧ (nPh n i : ℝ) / b n i ≤ 3 / 4 * ((B n : ℝ) + 7)) ∧
    (b n 1 : ℝ) ≤ (N n : ℝ) / 256 ∧ (256 / 7 : ℝ) < (m n : ℝ) / b n 1 ∧ (256 / 7 : ℝ) > 32 ∧
    L n ≤ Nat.log 2 n ∧ k n ≤ Nat.log 2 n ∧
    ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)),
      (∀ p < numPhases n, (runState n (ltOf x π σ) (phaseStart n p + 1)).alloc =
          (runState n (ltOf x π σ) (phaseStart n p)).alloc + phaseFresh n p) ∧
      ∀ t, T < t → t < n → (∀ p < numPhases n, phaseStart n p ≠ t) →
        (runState n (ltOf x π σ) (t + 1)).alloc = (runState n (ltOf x π σ) t).alloc := by sorry

end RandOrderSort
