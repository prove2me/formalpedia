-- Prove2me | Theorems.Thm_StallEconomy_Magnet_row_count
-- name    : StallEconomy.Magnet.row_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:04.590214+00:00
-- url     : https://prove2.me/theorems/e8053bfc-7ea0-4376-88ed-176bafff0754
-- title:
--   §3.3, p. 17 — every transition row counts all customer grid points
-- statement:
--   For any inner-diamond origin $z_o\in\mathcal I_0$, the sets $\mathcal A(z_o,z_d)$ count the customers sent to each possible next rendezvous. Their total count is the number of customer locations:
--   $$
--   \sum_{z_d\in\mathcal I_0}|\mathcal A(z_o,z_d)|=(k+1)^2.
--   $$
--
--   This count yields the unit row sums of the rendezvous transition matrix.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 17, paragraph before Theorem 1

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem row_count (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo : ℤ × ℤ) (hzo : zo ∈ inner k h) :
    ∑ zd : inner k h, (A k h zo zd.1).card = (k + 1) ^ 2 := by sorry

end StallEconomy.Magnet
