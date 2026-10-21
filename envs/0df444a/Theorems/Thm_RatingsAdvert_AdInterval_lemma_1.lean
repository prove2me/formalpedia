-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_lemma_1
-- name    : RatingsAdvert.AdInterval.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:40.641364+00:00
-- url     : https://prove2.me/theorems/37b537e7-f53b-469b-ac4f-4f71cbf66306
-- title:
--   Lemma 1, p. 38 (PDF 40) — the Benchmark equilibrium solves p^0_1 = (1+β−z^0τ)/2, p^0_2 = (1+β−τ)/2, ((1+β−z^0τ)/2)² = A′(z^0)
-- statement:
--   Fix a model $(\tau,\beta,A)$ satisfying the standing assumptions and the interiority condition, and consider the Benchmark case, in which second-generation consumers learn only that the product exists.
--
--   1. Every pure-strategy PBE $(z^0, p^0_1, p^0_2)$ has $z^0 \in (0,1)$ and solves
--   $$p^0_1 = \frac{1+\beta-z^0\tau}{2}, \qquad p^0_2 = \frac{1+\beta-\tau}{2}, \qquad \Big(\frac{1+\beta-z^0\tau}{2}\Big)^2 = A'(z^0).$$
--   2. Conversely, every $z \in [0,1]$ solving $\big((1+\beta-z\tau)/2\big)^2 = A'(z)$ (equation (7)) together with these prices is a PBE of the Benchmark case.
--
--   This characterizes the Benchmark equilibrium against which Proposition 1 compares the AR and Reviews cases.
--
--   **Formalization Note.** The converse half is the paper's argument that "$p^0_1$ and $z^0$ are chosen to maximize period 1 profits"; it makes the characterization usable for existence.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), p. 38 (PDF 40), Lemma 1 and its proof; eqs. (6)–(7), p. 14 (PDF 16)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem lemma_1 (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∀ z p1 p2 : ℝ, IsPBEBench P z p1 p2 →
        z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
          p2 = (1 + P.beta - P.tau) / 2 ∧
          ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        IsPBEBench P z ((1 + P.beta - z * P.tau) / 2) ((1 + P.beta - P.tau) / 2) := by sorry

end RatingsAdvert.AdInterval
