-- Prove2me | Theorems.Thm_QuantumLTF_Membership_bisection_resource_scale
-- name    : QuantumLTF.Membership.bisection_resource_scale
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T20:12:00.025716+00:00
-- url     : https://prove2.me/theorems/b009451f-32c7-42af-863b-74c8113ca9ee
-- title:
--   Absorbing bisection depth into logarithmic resource bounds
-- statement:
--   Let $A,q,U\ge0$ and $L\ge1$. If $q\le UL$, then the cost expression arising from $q$ reversible bisection rounds satisfies
--
--   $$
--   (A+q)^2(q+1)\le (U+1)^3(A+L)^2L.
--   $$
--
--   Thus a depth bound $q=O(L)$ can be absorbed into the standard quadratic workspace factor and one additional factor of $L$.
-- source:
--   Elementary resource-accounting inequality used in the proof of Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.2, pp. 25–26 (PDF pp. 26–27).

import Mathlib

namespace QuantumLTF.Membership

theorem bisection_resource_scale {A L U q : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hU : 0 ≤ U) (hq0 : 0 ≤ q)
    (hq : q ≤ U * L) :
    (A + q) ^ 2 * (q + 1) ≤ (U + 1) ^ 3 * (A + L) ^ 2 * L := by sorry

end QuantumLTF.Membership
