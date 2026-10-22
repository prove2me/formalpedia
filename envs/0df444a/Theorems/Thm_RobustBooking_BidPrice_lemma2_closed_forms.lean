-- Prove2me | Theorems.Thm_RobustBooking_BidPrice_lemma2_closed_forms
-- name    : RobustBooking.BidPrice.lemma2_closed_forms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:07:27.986932+00:00
-- url     : https://prove2.me/theorems/03e4ab5f-d62d-48f8-b940-130e7d9f551f
-- title:
--   Lemma 2 — closed forms (16) and (17) of P(q) and V(q) for the protection levels (15)
-- statement:
--   Let $0 < f_{\min} < f_{\max}$, $n > 0$, $r = f_{\min}/f_{\max}$ and $\rho = 1/(1 - \ln r)$. Let $\theta$ be the protection levels of Eq. (15), $Q(f) = n - \theta(f)$, $P(q) = \min\{f \in [f_{\min}, f_{\max}] : Q(f) \ge q\}$ and $V(q) = \int_0^q P(s)\,ds$. Then for $0 \le q \le n$,
--   $$P(q) = \begin{cases} f_{\min} & q < n\rho,\\ f_{\max}\, r^{(n-q)/(n(1-\rho))} & n\rho \le q \le n,\end{cases} \qquad V(q) = \begin{cases} q\, f_{\min} & q < n\rho,\\ \dfrac{n P(q)}{1 - \ln r} & n\rho \le q \le n.\end{cases}$$
--
--   These are Eqs. (16) and (17). The ratio $V(q)/(nP(q)) = 1/(1 - \ln r)$ on $[n\rho, n]$ is where the constant of Theorem 7 comes from.
--
--   **Formalization Note.** $P$ and $V$ are the definitions (through `sInf` and an interval integral), not the closed forms. The power $r^{(n-q)/(n(1-\rho))}$ is the real power `Real.rpow` with base $r \in (0,1)$; $\ln$ is `Real.log`. The first case is stated for $0 \le q < n\rho$ (the domain of $P$ and $V$ is $[0, n]$).
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 959, Lemma 2 (Eqs. (16), (17))

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

namespace RobustBooking.BidPrice

/-- Lemma 2 (Ball–Queyranne 2009, p. 959). Let `0 < f_min < f_max`, `n > 0`, `r = f_min / f_max`
and `ρ = 1 / (1 - ln r)`. If `θ(f)` is defined by Eq. (15), then the order quantity control
function `P` and the value accumulation function `V(q) = ∫₀^q P(s) ds` satisfy, for `0 ≤ q ≤ n`,
Eq. (16): `P(q) = f_min` for `q < nρ` and `P(q) = f_max r^((n - q)/(n(1 - ρ)))` for
`nρ ≤ q ≤ n`; and Eq. (17): `V(q) = q f_min` for `q < nρ` and `V(q) = n P(q) / (1 - ln r)` for
`nρ ≤ q ≤ n`. -/
theorem lemma2_closed_forms (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (q : ℝ) :
    (0 ≤ q → q < n * rho (discountRatio fmin fmax) →
      bidPriceP fmin fmax n q = fmin ∧ valueAccumulation fmin fmax n q = q * fmin) ∧
    (n * rho (discountRatio fmin fmax) ≤ q → q ≤ n →
      bidPriceP fmin fmax n q =
          fmax * discountRatio fmin fmax ^
            ((n - q) / (n * (1 - rho (discountRatio fmin fmax)))) ∧
        valueAccumulation fmin fmax n q =
          n * bidPriceP fmin fmax n q / (1 - Real.log (discountRatio fmin fmax))) := by sorry

end RobustBooking.BidPrice
