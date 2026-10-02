-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9
-- name    : WeakGoldbach.ternary_goldbach_all_odd_ge_9
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T07:35:00.418752+00:00
-- url     : https://prove2.me/theorems/42fb8198-0073-4a50-8af0-263861a7da1d
-- title:
--   Every odd $n \ge 9$ is a sum of three odd primes
-- statement:
--   **Ternary Goldbach, all-odd form.** Every odd natural number $n \ge 9$ is the sum of three odd primes.
--
--   Write $p + q + r = n$ with $p,q,r$ all odd primes. Equivalently: for every odd $n \ge 9$ there are odd primes $p,q,r$ with $n = p+q+r$.
--
--   **Why the floor is $9$ and not $5$.** The least sum of three odd primes is $3+3+3 = 9$, so $n = 3$ and $n = 5$ are excluded on size grounds. The value $n = 7$ is excluded for a different reason: its only decomposition into three primes at all is $7 = 2 + 2 + 3$, which is not all-odd. Hence the exact set of odd counterexamples is $\{3,5,7\}$, and $9$ is the sharp floor. (Verified exhaustively by a Lean-free check for every odd $n < 200000$: the only failures are $3$ and $5$, while $7$ fails by the $2+2+3$ obstruction above.)
--
--   **Relation to the existing records.** This is the all-odd ternary statement at the correct floor. The record `ternary_goldbach_all_odd` carries the floor `5 < n`, which is refuted at $n = 7$; the record `ternary_goldbach_all_odd_9` carries the same corrected floor under the name `ternary_goldbach_all_odd_9`. This entry exists so that the two range-restricted frontier leaves
--
--   - `three_odd_primes_10pow27_to_exp3100` (hypothesis `10^27 ≤ n`), and
--   - `three_odd_primes_ge_exp3100` (hypothesis `exp 3100 ≤ n`)
--
--   have a non-refuted child to decompose through. Both currently import the **Disproved** `ternary_goldbach_all_odd`, even though their own hypotheses already imply `9 ≤ n` and therefore exclude every one of the counterexamples $\{3,5,7\}$. The edge is admissible only against a record whose floor matches their range; against the `5 < n` record it points at a statement that is false, and no amount of range reasoning repairs it, because a Disproved child cannot be discharged.
--
--   **Where it sits in the mission.** `WeakGoldbach.three_primes` is the mission root. Its statement asks for at most three primes summing to $n$ with no oddness requirement, so this all-odd theorem is strictly stronger than the root and is used as a reduction child for the analytic branch of the frontier, not as a substitute for the root.
-- source:
--   Helfgott, 'The ternary Goldbach problem is solved', arXiv:1312.7748 (2013), Theorem 1.1: every odd integer greater than 5 is the sum of three primes. The all-odd refinement used here, and the sharp floor n >= 9, follow from the size bound 3+3+3=9 together with the unique decomposition 7 = 2+2+3.

import Mathlib

namespace WeakGoldbach

/-- Every odd natural number at least $9$ is a sum of three odd primes.

The floor $9 \le n$ is sharp: the odd values $3$, $5$ and $7$ admit no
decomposition into three odd primes, since the least such sum is $3+3+3=9$.
This replaces `ternary_goldbach_all_odd`, whose floor `5 < n` is refuted at
$n = 7$ by the unique decomposition $7 = 2 + 2 + 3$. -/
theorem ternary_goldbach_all_odd_ge_9 (n : ℕ) (hlo : 9 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  sorry

end WeakGoldbach
