-- Prove2me | Theorems.Thm_ThreeSumSharpTail_full_d_call_balance
-- name    : ThreeSumSharpTail.full_d_call_balance
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:52:17.861004+00:00
-- url     : https://prove2.me/theorems/bc896139-6061-43b1-8210-c82908eab334
-- title:
--   Full dimension host call factors preserve the desired saving
-- statement:
--   If D,n>=1, 0<=s<=1/2, D^(s/2)<=g<=2D^(s/2), and D^(1+s)<=n, then the full dimension preprocessing, query, overhead, construction and scan factors are bounded respectively by 2D^(-s/2), 2D^(-s/2), 2D^(-s/2), 2nD^(-s/2), and D^(-s/2). This is an elementary real-power balance lemma, without any additional program or runtime assumption.
-- source:
--   Derived auxiliary algebraic bounds for Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis, Sections 3-4, composed with the full-D Theorem 17 host.

import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.full_d_call_balance (D n g s : ℝ)
    (hD : 1 ≤ D) (_hn : 1 ≤ n) (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : D ^ (s / 2) ≤ g) (hgHi : g ≤ 2 * D ^ (s / 2))
    (hbuild : D ^ (1 + s) ≤ n) :
    g / D ^ s ≤ 2 * D ^ (-s / 2) ∧
    g * D ^ (1 / 2 - s) / Real.sqrt D ≤ 2 * D ^ (-s / 2) ∧
    g / Real.sqrt D ≤ 2 * D ^ (-s / 2) ∧
    g * D ≤ 2 * n * D ^ (-s / 2) ∧
    1 / g ≤ D ^ (-s / 2) := by sorry
