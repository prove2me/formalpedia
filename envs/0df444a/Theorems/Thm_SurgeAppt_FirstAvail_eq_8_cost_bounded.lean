-- Prove2me | Theorems.Thm_SurgeAppt_FirstAvail_eq_8_cost_bounded
-- name    : SurgeAppt.FirstAvail.eq_8_cost_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:38.107442+00:00
-- url     : https://prove2.me/theorems/309f898d-6c9c-4db7-89df-f4e659a699eb
-- title:
--   (8), p. 10 — the expected one-period cost is bounded by $\bar h + c_F(\beta DK + K + M)$
-- statement:
--   Consider the appointment-scheduling model of §3 under its standing assumptions: horizon $D\ge1$, capacity $K = K_b + K_s$ per period, at most $M$ requests per period, surge cost $c_s\ge0$, failure cost $c_F>0$ and discount factor $\beta\in(0,1)$. Let $\mathbf S$ be a valid appointment book, $a\le M$ the number of requests, and $\mathbf u$ an admissible action in the sense of (1). Then the expected one-period cost (7) satisfies
--
--   $$
--   0\le \mathbb E\big[g(\mathbf S,\mathbf U)\big] \le \bar h + c_F\big(\beta D K + K + M\big),\qquad \bar h = h(K) = c_s\max\{K-K_b,0\}.
--   $$
--
--   Bounded, nonnegative one-period costs make the discounted value (9) of every admissible policy a convergent series; this is the boundedness the paper invokes before the Bellman equation (11).
--
--   **Formalization Note** The lower bound $0\le g$ is added to the page's statement; it holds because every term of (7) is nonnegative.
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), p. 10, (8)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

namespace SurgeAppt.FirstAvail

/-- (8), p. 10: under the standing assumptions, at a valid state with at most `M` requests and an
admissible action, the expected one-period cost (7) is bounded by
`h̄ + c_F (β D K + K + M)` with `h̄ = h(K)`; it is also nonnegative (added). -/
theorem eq_8_cost_bounded (P : Params) (hP : P.Standing) (s : Book P) (hs : Valid P s)
    (a : ℕ) (ha : a ≤ P.M) (u : Book P) (hu : Admissible P s a u) :
    0 ≤ cost P s a u ∧
      cost P s a u ≤ hcost P P.K + P.cF * (P.β * P.D * P.K + P.K + P.M) := by sorry

end SurgeAppt.FirstAvail
