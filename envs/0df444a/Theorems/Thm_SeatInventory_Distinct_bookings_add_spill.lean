-- Prove2me | Theorems.Thm_SeatInventory_Distinct_bookings_add_spill
-- name    : SeatInventory.Distinct.bookings_add_spill
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:05:06.57033+00:00
-- url     : https://prove2.me/theorems/b6384442-bfd7-4536-9582-7fe35c3659a1
-- title:
--   Eq. (5.6) — expected bookings plus expected spill equal expected requests
-- statement:
--   Let the number of requests $r$ for a fare class take values in $\{0,1,2,\dots\}$ with finite mean $\bar r = E[r]$. For every number $S$ of seats allocated to the class, with expected bookings $\bar b(S) = E[\min(r,S)]$ and expected spill $\bar l(S) = E[(r-S)^+]$,
--   $$
--   \bar b(S) + \bar l(S) = \bar r.
--   $$
--
--   Every request is either booked or refused, so the expected numbers of booked and refused requests account for all expected demand. The identity turns an expected-spill estimate into an expected-load estimate and back.
--
--   **Formalization Note** The thesis assumes the mean of the request distribution exists without saying so; the Lean statement assumes it explicitly (`Summable (fun r => (p r).toReal * r)`), since otherwise Lean's series for $\bar l$ and $\bar r$ default to $0$. Requests are integer valued (`PMF ℕ`).
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 103, Eqs. (5.3)-(5.6)

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (5.6), p. 103: for a fare class with integer requests `r` of finite mean,
expected bookings plus expected spill equal expected requests, `b̄(S) + l̄(S) = r̄`, for every
allocation `S`. -/
theorem bookings_add_spill (p : PMF ℕ) (hmean : Summable (fun r : ℕ => (p r).toReal * (r : ℝ)))
    (S : ℕ) :
    expectedBookings p S + expectedSpill p S = meanRequests p := by sorry

end SeatInventory.Distinct
