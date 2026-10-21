-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_period2_price
-- name    : RatingsAdvert.AdInterval.period2_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:46.943968+00:00
-- url     : https://prove2.me/theorems/01d6e25f-e169-42e5-a81b-40fdd0ed5579
-- title:
--   §3.1.2, p. 14 (PDF 16) — the optimal second-period prices p^0_2 = (1+β−τ)/2 and (1+βx−τ)/2
-- statement:
--   In period 2 the firm chooses $p_2$ to maximize $p_2 D_2(p_2)$. For every model and every information value $x$ (inferred quality $q^e$ in the AR case, true quality $q$ in the Reviews case), a price $p$ maximizes second-period profit over all real prices exactly when it equals the first-order solution:
--   $$p = \arg\max_{p'} p'(1+\beta-\tau-p') \iff p = \frac{1+\beta-\tau}{2},$$
--   $$p = \arg\max_{p'} p'(1+\beta x-\tau-p') \iff p = \frac{1+\beta x-\tau}{2}.$$
--
--   This pins down the second-period price in all three information structures, and with it the second-period profit $\big((1+\beta x-\tau)/2\big)^2$ that enters the firm's first-period problem.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), p. 14 (PDF 16), §3.1.2; proof of Lemma 2, p. 38 (PDF 40); proof of Lemma 3, p. 41 (PDF 43)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem period2_price (P : Params) (x p : ℝ) :
    ((∀ p' : ℝ, p' * D2Bench P p' ≤ p * D2Bench P p) ↔ p = (1 + P.beta - P.tau) / 2) ∧
      ((∀ p' : ℝ, p' * D2Info P x p' ≤ p * D2Info P x p) ↔
        p = (1 + P.beta * x - P.tau) / 2) := by sorry

end RatingsAdvert.AdInterval
