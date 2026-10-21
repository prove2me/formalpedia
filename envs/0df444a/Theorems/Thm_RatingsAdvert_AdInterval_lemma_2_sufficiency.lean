-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_lemma_2_sufficiency
-- name    : RatingsAdvert.AdInterval.lemma_2_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:53.463774+00:00
-- url     : https://prove2.me/theorems/e048aabd-4ba3-471a-84e3-c77d56a20b29
-- title:
--   Proof of Lemma 2, pp. 40–41 (PDF 42–43) — the root of (8) survives large deviations: it is an AR equilibrium
-- statement:
--   Fix a model satisfying the standing assumptions and the interiority condition. If $z \in [0,1]$ solves the AR first-order condition (8),
--   $$\Big(\frac{1+\beta-z\tau}{2}\Big)^2 - \frac{\tau(1+\beta-\tau)}{2} = A'(z),$$
--   then the advertising interval $z$, the first-period price $p_1 = (1+\beta-z\tau)/2$ and the second-period pricing rule $p_2(x) = (1+\beta x-\tau)/2$ (as a function of the inferred quality $x$) form a pure-strategy PBE of the Average Rating case: no deviation $(z', p')$ with $z' \in [0,1]$, local or large, raises the firm's expected profit when consumers hold the belief $z^e = z$.
--
--   This is the sufficiency half of the paper's proof of Lemma 2 ("we are left to prove that the resulting $z$ survives large deviations"); together with the uniqueness of the root of (8) it gives existence and uniqueness of the AR equilibrium.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), proof of Lemma 2, pp. 40–41 (PDF 42–43)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem lemma_2_sufficiency (P : Params) (hS : P.Standing) (hI : P.Interior) (z : ℝ)
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (h8 : ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z) :
    IsPBEAR P z ((1 + P.beta - z * P.tau) / 2) (fun x => (1 + P.beta * x - P.tau) / 2) := by sorry

end RatingsAdvert.AdInterval
