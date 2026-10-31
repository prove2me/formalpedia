-- Prove2me | Theorems.Thm_RobustBooking_BidPrice_theorem7_bid_price_competitive
-- name    : RobustBooking.BidPrice.theorem7_bid_price_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:07:56.478759+00:00
-- url     : https://prove2.me/theorems/a4434158-8b8a-4d1d-8f15-5c397f394a96
-- title:
--   Theorem 7 — with θ(f) from (15), both bid-price policies A_θ and A′_θ are at least 1/(1 − ln r)-competitive
-- statement:
--   Let $0 < f_{\min} < f_{\max}$, $r = f_{\min}/f_{\max}$ and capacity $n > 0$, and let $\theta$ be the protection levels of Eq. (15),
--   $$\theta(f) = \frac{\ln f_{\max} - \ln f}{\ln f_{\max} - \ln f_{\min}}\Big(1 - \frac{1}{1 - \ln r}\Big)n,$$
--   with $Q(f) = n - \theta(f)$ and $P$ its order quantity control function. Then for every instance $I$ whose fares all lie in $[f_{\min}, f_{\max}]$, the protection-level control policy $A_\theta$ based on $Q$ and the order quantity control policy $A'_\theta$ based on $P$ both satisfy
--   $$v'(I) \ge \frac{1}{1 - \ln r}\, v^*(I),$$
--   i.e. both achieve competitive ratio at least $1/(1 - \ln r)$.
--
--   With Theorem 6 this makes the bid-price policies of Eq. (15) optimal among all online booking policies, deterministic or randomized, for the continuous bid-price problem.
--
--   **Formalization Note.** "Competitive ratio at least $c$" is stated per instance as $c\, v^*(I) \le v'(I)$, which is equivalent to $\mathrm{CR} \ge c$ and avoids the `sInf`. $v^*$ is the true offline maximum (`sSup`), the policies are the paper's sup rules (the protection constraint over the whole continuum $[O, f_{\max}]$), and requests are sized, with the paper's unit orders as `qty = 1`. The hypothesis that fares lie in $[f_{\min}, f_{\max}]$ is part of the problem and cannot be dropped.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 959, Theorem 7

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

namespace RobustBooking.BidPrice

/-- Theorem 7 (Ball–Queyranne 2009, p. 959). For the continuous bid-price control problem with
fares `0 < f_min < f_max`, `r = f_min / f_max`, and capacity `n > 0`, if `θ(f)` is defined by
Eq. (15), then the protection-level control policy `A_θ` based on `Q(f) = n - θ(f)` and the order
quantity control policy `A′_θ` based on `P(q)` both achieve competitive ratios of at least
`1 / (1 - ln r)`: on every instance whose fares all lie in `[f_min, f_max]`, each earns at least
`1 / (1 - ln r)` times the optimal offline revenue. -/
theorem theorem7_bid_price_competitive (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (I : List Request) (hI : FaresIn (Set.Icc fmin fmax) I) :
    1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
        revenue n (protectionLevelPolicy fmax (protectionControl fmin fmax n)) I ∧
      1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
        revenue n (orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)) I := by sorry

end RobustBooking.BidPrice
