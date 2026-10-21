-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_lemma_3
-- name    : RatingsAdvert.AdInterval.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:49.499576+00:00
-- url     : https://prove2.me/theorems/65d59509-7e54-43b1-8890-c9667196db9a
-- title:
--   Lemma 3, p. 41 (PDF 43) — the Reviews equilibrium solves (7) with p^R_1 = (1+β−z^Rτ)/2, p^R_2 = (1+βq−τ)/2; p^R_1 = p^0_1 < p^AR_1, z^R = z^0 > z^AR
-- statement:
--   Fix a model $(\tau,\beta,A)$ satisfying the standing assumptions and the interiority condition, and consider the Reviews case, in which second-generation consumers learn the true quality $q$.
--
--   1. Every pure-strategy PBE $(z^R, p^R_1, p^R_2)$ has $z^R \in (0,1)$ and solves
--   $$p^R_1 = \frac{1+\beta-z^R\tau}{2}, \qquad p^R_2(q) = \frac{1+\beta q-\tau}{2}\ \ (q \in [0,2]), \qquad \Big(\frac{1+\beta-z^R\tau}{2}\Big)^2 = A'(z^R).$$
--   Moreover, for every Benchmark PBE $(z^0, p^0_1, p^0_2)$ we have $z^R = z^0$ and $p^R_1 = p^0_1$, and for every AR PBE $(z^{AR}, p^{AR}_1, p^{AR}_2)$ we have $z^{AR} < z^R$ and $p^R_1 < p^{AR}_1$.
--   2. Conversely, every $z \in [0,1]$ solving (7), together with these prices, is a PBE of the Reviews case.
--
--   **Formalization Note.** The converse half follows the proof's observation that the second-period profit does not depend on $(z, p_1)$, so $z^R$ and $p^R_1$ maximize first-period profit; it supplies existence.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), p. 41 (PDF 43), Lemma 3 and its proof

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem lemma_3 (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∀ (z p1 : ℝ) (p2 : ℝ → ℝ), IsPBERev P z p1 p2 →
        z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
          (∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) ∧
          ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z ∧
          (∀ z0 p10 p20 : ℝ, IsPBEBench P z0 p10 p20 → z = z0 ∧ p1 = p10) ∧
          ∀ (zA p1A : ℝ) (p2A : ℝ → ℝ), IsPBEAR P zA p1A p2A → zA < z ∧ p1 < p1A) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        IsPBERev P z ((1 + P.beta - z * P.tau) / 2) (fun x => (1 + P.beta * x - P.tau) / 2) := by sorry

end RatingsAdvert.AdInterval
