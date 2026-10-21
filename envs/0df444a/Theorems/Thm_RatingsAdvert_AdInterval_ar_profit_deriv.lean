-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_ar_profit_deriv
-- name    : RatingsAdvert.AdInterval.ar_profit_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:51.659299+00:00
-- url     : https://prove2.me/theorems/9800561f-6545-46d2-8302-e1cd7b87da3c
-- title:
--   Proof of Lemma 2, p. 39 (PDF 41) — at z = z^e the AR expected second-period profit has derivative −τ(1+β−τ)/2 in z
-- statement:
--   Fix a model satisfying the standing assumptions and a belief $z^e \in [0,1]$. In the AR case, if the firm advertises to an interval $z$, second-generation consumers infer the quality $q^e(q, z) = \min\{\max\{0, (\beta q - \tau(z-z^e))/\beta\}, 2\}$, and the firm, pricing optimally in period 2, earns $\big((1+\beta q^e-\tau)/2\big)^2$. The expected second-period profit
--   $$H(z) = E_q\Big[\Big(\frac{1+\beta q^e(q,z)-\tau}{2}\Big)^2\Big], \qquad q \sim U[0,2],$$
--   is differentiable at $z = z^e$ with
--   $$H'(z^e) = -\frac{\tau(1+\beta-\tau)}{2}.$$
--
--   This is the extra term of the AR advertising first-order condition (8): the paper computes $E_q\big((q^e\beta-\tau+1)\beta\,\partial q^e/\partial z \mid z = z^e\big) = -\tau(1-\tau+\beta)$, which enters condition (11) with the factor $1/2$.
--
--   **Formalization Note.** The second-period profit is written in its optimized closed form $\big((1+\beta x-\tau)/2\big)^2$, the value of $p_2 D^{AR}_2(p_2)$ at the optimal price of the milestone on second-period prices. The clamp of footnote 10 makes $q^e$ only piecewise differentiable in $z$; the statement asserts two-sided differentiability of the expectation at $z = z^e$.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), proof of Lemma 2, pp. 39–40 (PDF 41–42), display for z = z^e and eq. (11)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem ar_profit_deriv (P : Params) (hS : P.Standing) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun z' : ℝ => expQ (fun q => ((1 + P.beta * qe P q z' z - P.tau) / 2) ^ 2))
      (-(P.tau * (1 + P.beta - P.tau) / 2)) z := by sorry

end RatingsAdvert.AdInterval
