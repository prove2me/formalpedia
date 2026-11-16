-- Prove2me | Theorems.Thm_PHIP1887_central_negative_step
-- name    : PHIP1887.central_negative_step
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T17:43:14.952944+00:00
-- url     : https://prove2.me/theorems/759ff083-cfa7-474b-b7d1-d0b6b4d89de8
-- title:
--   Negative propagation in a central recurrence
-- statement:
--   Let $k,a,b,c$ be real numbers with $k>0$, $a<0$, and $c\ge0$. Then
--
--   $$c=k^2a-2k(2k+1)b\quad\Longrightarrow\quad b<0.$$
--
--   This elementary algebraic implication is a reusable sign-propagation step for recurrences. Its application to a family of functions requires the recurrence and the sign assumptions to be established independently. No assertion about the Riemann hypothesis is part of this statement.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno, PHIP-1887, declaration central_negative_step in PHIP-1887_AXLE.lean. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9 . Elementary algebraic lemma; no novelty claim.

import Mathlib

theorem PHIP1887.central_negative_step (k a b c : ℝ) (hk : 0 < k)
    (ha : a < 0) (hc : 0 ≤ c)
    (heq : c = k^2*a - 2*k*(2*k+1)*b) : b < 0 := by sorry
