-- Prove2me | Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg08
-- name    : WeakGoldbach.helfgott_platt_block_ladders_grp01_sg08
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:20:23.207169+00:00
-- url     : https://prove2.me/theorems/8bc3194b-a4a7-4c57-899c-ce0a0ad6a9fe
-- title:
--   Helfgott–Platt block ladders, group 1 subgroup 8 of 10
-- statement:
--   Put $H = 2\cdot 10^{18}$ and $W = 2^{54}\cdot 10^9 = 18014398509481984000000000$. For every integer $b$ in the range
--
--   $$
--   $34489 \le b < 39416$,
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
--   Role: this is subgroup $8$ of $10$ consecutive subgroups of `WeakGoldbach.helfgott_platt_block_ladders_grp01`, which covers block indices $0 \le b < 49270$ (group 1 of 10 of the parent `WeakGoldbach.helfgott_platt_block_ladders`). Each subgroup has width $4927$ in the block index $b$. The subgroups meet end to end within group 1.
--
--   This isolates the local computational certificate for $4927$ of the $492700$ intervals of width $W$ reported in Section 4 of the source. The endpoint conditions allow consecutive blocks to be joined without a gap of size $2H$.
--
--   The hypotheses are $34489 \le b < 39416$. No certificate data are supplied here; the statement is an open certificate obligation for this index range.
--
--   **Formalization Note** The conclusion matches `WeakGoldbach.helfgott_platt_block_ladders_grp01` exactly; only the range of $b$ is restricted.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, Section 3 (prime ladder algorithm) and Section 4 (width 2^54*10^9, endpoint distances 2*10^18, and 492700 intervals). https://arxiv.org/pdf/1305.3062. Subgroup 8 of 10 of WeakGoldbach.helfgott_platt_block_ladders_grp01 covering block indices [34489, 39416).

import Mathlib.Data.Nat.Prime.Basic

theorem WeakGoldbach.helfgott_platt_block_ladders_grp01_sg08 (b : ℕ) (hb_lo : 34489 ≤ b) (hb_hi : b < 39416) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      (b*18014398509481984000000000 < p 0 ∧
        p 0 ≤ b*18014398509481984000000000 + 2*10^18) ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + 4*10^18) ∧
      (p k ≤ (b+1)*18014398509481984000000000 ∧
        (b+1)*18014398509481984000000000 < p k + 2*10^18) := by sorry
