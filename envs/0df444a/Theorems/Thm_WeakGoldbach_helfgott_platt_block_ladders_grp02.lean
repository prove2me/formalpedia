-- Prove2me | Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp02
-- name    : WeakGoldbach.helfgott_platt_block_ladders_grp02
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:17:43.208982+00:00
-- url     : https://prove2.me/theorems/1b45c163-f428-4b8e-b6d0-91dd8d82631c
-- title:
--   Helfgott–Platt block ladders, group 2 of 10
-- statement:
--   Put $H = 2\cdot 10^{18}$ and $W = 2^{54}\cdot 10^9 = 18014398509481984000000000$. For every integer $b$ in the range
--
--   $$
--   $49270 \le b < 98540$,
--   $$
--
--   there is a finite increasing sequence of primes $p_0,\ldots,p_k$ satisfying
--
--   $$
--   bW < p_0 \le bW + H,\qquad p_i < p_{i+1} < p_i + 2H \quad (0 \le i < k),
--   $$
--
--   $$
--   p_k \le (b+1)W < p_k + H.
--   $$
--
--   Role: this is group $2$ of $10$ consecutive groups of Helfgott–Platt computation blocks covering $0 \le b < 492700$. Each group has width $49270$ in the block index $b$. The groups meet end to end: group $j$'s upper endpoint is group $j+1$'s lower endpoint, the first lower endpoint is $0$, and the last upper endpoint is $492700$.
--
--   This isolates the local computational certificate for $49270$ of the $492700$ intervals of width $W$ reported in Section 4 of the source. The endpoint conditions allow consecutive blocks (and consecutive groups) to be joined without a gap of size $2H$.
--
--   The hypotheses are $49270 \le b < 98540$. No certificate data are supplied here; the statement is an open certificate obligation for this index range.
--
--   **Formalization Note** The conclusion matches the parent `WeakGoldbach.helfgott_platt_block_ladders` exactly; only the range of $b$ is restricted.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, Section 3 (prime ladder algorithm) and Section 4 (width 2^54*10^9, endpoint distances 2*10^18, and 492700 intervals). https://arxiv.org/pdf/1305.3062. Group 2 of 10 consecutive partitions of the parent WeakGoldbach.helfgott_platt_block_ladders covering block indices [49270, 98540).

import Mathlib.Data.Nat.Prime.Basic

theorem WeakGoldbach.helfgott_platt_block_ladders_grp02 (b : ℕ) (hb_lo : 49270 ≤ b) (hb_hi : b < 98540) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      (b*18014398509481984000000000 < p 0 ∧
        p 0 ≤ b*18014398509481984000000000 + 2*10^18) ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + 4*10^18) ∧
      (p k ≤ (b+1)*18014398509481984000000000 ∧
        (b+1)*18014398509481984000000000 < p k + 2*10^18) := by sorry
