-- Prove2me | Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders
-- name    : WeakGoldbach.helfgott_platt_block_ladders
-- status  : Open
-- author  : @suzukasan
-- created : 2026-10-20T16:32:15.912608+00:00
-- url     : https://prove2.me/theorems/2f45542c-d6fc-4830-b9d8-be5c0baaf988
-- title:
--   Local prime ladders in the 492700 Helfgott–Platt computation blocks
-- statement:
--   Put $H=2\cdot10^{18}$ and $W=2^{54}10^9=18014398509481984000000000$. For each integer $0\le b<492700$, there is a finite increasing sequence of primes $p_0,\ldots,p_k$ satisfying
--
--   $$bW<p_0\le bW+H,\qquad p_i<p_{i+1}<p_i+2H\quad(0\le i<k),$$
--
--   $$p_k\le(b+1)W<p_k+H.$$
--
--   This is the local computational certificate for one of the intervals in the Helfgott–Platt verification. The intervals have exactly the width and count reported in Section 4, and their total length is the target endpoint $T$. The endpoint conditions allow consecutive blocks to be joined without a gap of size $2H$.
--
--   The theorem is an open certificate obligation. No actual certificate data are supplied here. The source reports mixed Proth-prime and general-prime rungs, with independent Proth and ECPP checks; it does not supply a Lean proof. The strict internal gap is the search condition in Section 3. The strict final margin follows from the reported distance at most $H$, since equality would make the final prime the even integer $(b+1)W-H>2$.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, Section 3 (prime ladder algorithm, pp. 2) and Section 4 (width 2^54*10^9, endpoint distances 2*10^18, and 492700 intervals, p. 3). https://arxiv.org/pdf/1305.3062. This theorem isolates the reported local computations as an unproved certificate obligation; it does not claim to reproduce or verify the missing data.

import Mathlib.Data.Nat.Prime.Basic

theorem WeakGoldbach.helfgott_platt_block_ladders (b : ℕ) (hb : b < 492700) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      (b*18014398509481984000000000 < p 0 ∧
        p 0 ≤ b*18014398509481984000000000 + 2*10^18) ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + 4*10^18) ∧
      (p k ≤ (b+1)*18014398509481984000000000 ∧
        (b+1)*18014398509481984000000000 < p k + 2*10^18) := by sorry
