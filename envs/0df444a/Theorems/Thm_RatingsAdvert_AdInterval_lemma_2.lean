-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_lemma_2
-- name    : RatingsAdvert.AdInterval.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:47.255988+00:00
-- url     : https://prove2.me/theorems/b5bcdfdd-f51c-4ba8-b247-75de430370b1
-- title:
--   Lemma 2, p. 38 (PDF 40) — the AR equilibrium solves (8) with p^AR_1 = (1+β−z^ARτ)/2, p^AR_2 = (1+βq^e−τ)/2; z^AR < z^0, p^AR_1 > p^0_1
-- statement:
--   Fix a model $(\tau,\beta,A)$ satisfying the standing assumptions and the interiority condition, and consider the Average Rating case. Let $(z^{AR}, p^{AR}_1, p^{AR}_2)$ be a pure-strategy PBE, where $p^{AR}_2$ is the second-period price as a function of the inferred quality. Then
--
--   1. $z^{AR} \in (0,1)$ and $p^{AR}_1 = \dfrac{1+\beta-z^{AR}\tau}{2}$;
--   2. $p^{AR}_2(x) = \dfrac{1+\beta x-\tau}{2}$ for every inferred quality $x \in [0,2]$;
--   3. $z^{AR}$ solves (8):
--   $$\Big(\frac{1+\beta-z^{AR}\tau}{2}\Big)^2 - \frac{\tau(1+\beta-\tau)}{2} = A'(z^{AR});$$
--   4. for every PBE $(z^0, p^0_1, p^0_2)$ of the Benchmark case, $z^{AR} < z^0$ and $p^{AR}_1 > p^0_1$.
--
--   The comparison in item 4 is the core of Proposition 1: because consumers read a larger ad interval as lower quality, the firm advertises less and prices higher under an average rating.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), p. 38 (PDF 40), Lemma 2; proof pp. 38–40 (PDF 40–42)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem lemma_2 (P : Params) (hS : P.Standing) (hI : P.Interior) (z p1 : ℝ) (p2 : ℝ → ℝ)
    (h : IsPBEAR P z p1 p2) :
    z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) ∧
      ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z ∧
      ∀ z0 p10 p20 : ℝ, IsPBEBench P z0 p10 p20 → z < z0 ∧ p10 < p1 := by sorry

end RatingsAdvert.AdInterval
