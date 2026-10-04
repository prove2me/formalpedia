-- Prove2me | Theorems.Thm_SeatInventory_Distinct_emsr_marginal_revenue
-- name    : SeatInventory.Distinct.emsr_marginal_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:05:13.131479+00:00
-- url     : https://prove2.me/theorems/c4134946-9a48-4a19-bed4-ef175418b33e
-- title:
--   Eq. (5.11) — the expected marginal revenue of the S-th seat is f · P[r ≥ S]
-- statement:
--   Let a fare class have average fare $f$ and integer-valued requests $r$, and let $\bar R(S) = f\cdot E[\min(r,S)]$ be its expected revenue when it holds $S$ seats. For every $S \ge 1$, the expected revenue added by the $S$-th seat is
--   $$
--   \bar R(S) - \bar R(S-1) = f \cdot P[r \ge S] = \mathrm{EMSR}(S).
--   $$
--
--   This identifies the expected marginal seat revenue of the thesis with an actual increment of expected revenue, which is what allows seats to be valued one at a time.
--
--   **Formalization Note** Stated for $S+1$ with $S\ge 0$, so no natural-number subtraction occurs. Discrete reading: requests are a `PMF ℕ` and $\bar P(S) = P[r\ge S]$ (Eq. (6.2), and the prose of (5.11), "the probability of selling $S_i$ or more seats"); with the $P[r>S]$ of Eq. (5.2) the identity would be false for integer demand. No assumption on the sign of $f$ or on the mean of $r$ is needed.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 105, Eq. (5.11)

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (5.11), p. 105: the expected marginal revenue of the `S`-th seat of a
fare class, `S ≥ 1`, is `f · P[r ≥ S]`: `R̄(S) − R̄(S − 1) = EMSR(S)`, written here with
`S + 1` in place of `S` so that `S + 1 ≥ 1`. -/
theorem emsr_marginal_revenue (f : ℝ) (p : PMF ℕ) (S : ℕ) :
    expectedRevenue f p (S + 1) - expectedRevenue f p S = emsr f p (S + 1) := by sorry

end SeatInventory.Distinct
