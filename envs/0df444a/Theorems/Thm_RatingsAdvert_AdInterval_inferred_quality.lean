-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_inferred_quality
-- name    : RatingsAdvert.AdInterval.inferred_quality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:55.319817+00:00
-- url     : https://prove2.me/theorems/c19824a7-be50-403d-947d-f705e4a6b868
-- title:
--   Eq. (3), p. 12 (PDF 14) — quality inferred from the average rating: q^e = (βq − τ(z − z^e))/β
-- statement:
--   In the Average Rating case second-generation consumers observe the mean net utility $\mu_1$ of first-generation buyers, given by (2),
--   $$\mu_1(q, z) = \frac{1 + \beta(2q-1) - (2z - z^e)\tau - p_1}{2},$$
--   where $q$ is the true quality, $z$ the advertising interval actually chosen, $z^e$ the consumers' belief about it and $p_1$ the observed first-period price. Consumers invert $\mu_1$ as if the interval were their belief $z^e$. Let $\beta > 0$. Then a quality $q'$ reproduces the observed rating at the believed interval exactly when it equals the inferred quality of (3):
--   $$\mu_1(q', z^e) = \mu_1(q, z) \iff q' = \frac{\beta q - \tau(z - z^e)}{\beta}.$$
--   Moreover, when this value lies in $[0,2]$ it coincides with the clamped inferred quality $q^e = \min\{\max\{0, (\beta q - \tau(z-z^e))/\beta\}, 2\}$ of footnote 10.
--
--   This is the inference that makes the AR case differ from the others: the inferred quality falls when the firm advertises to a larger interval than consumers believe.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), p. 12 (PDF 14), eq. (3) and footnote 10

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem inferred_quality (P : Params) (hβ : 0 < P.beta) (q z ze p1 q' : ℝ) :
    (mu1 P q' ze ze p1 = mu1 P q z ze p1 ↔ q' = (P.beta * q - P.tau * (z - ze)) / P.beta) ∧
      ((P.beta * q - P.tau * (z - ze)) / P.beta ∈ Set.Icc (0 : ℝ) 2 →
        qe P q z ze = (P.beta * q - P.tau * (z - ze)) / P.beta) := by sorry

end RatingsAdvert.AdInterval
