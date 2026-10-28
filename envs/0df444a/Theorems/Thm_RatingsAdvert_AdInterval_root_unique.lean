-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_root_unique
-- name    : RatingsAdvert.AdInterval.root_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:46.701191+00:00
-- url     : https://prove2.me/theorems/874a7d0d-4ce3-4267-ad05-2faff000c0cd
-- title:
--   Proof of Lemma 2, p. 40 (PDF 42) — each of the first-order conditions (7) and (8) has a unique root in [0,1], and it is interior
-- statement:
--   Fix a model satisfying the standing assumptions and the interiority condition. The Benchmark advertising condition (7)
--   $$\Big(\frac{1+\beta-z\tau}{2}\Big)^2 = A'(z)$$
--   has exactly one solution $z \in [0,1]$, and the AR advertising condition (8)
--   $$\Big(\frac{1+\beta-z\tau}{2}\Big)^2 - \frac{\tau(1+\beta-\tau)}{2} = A'(z)$$
--   has exactly one solution $z \in [0,1]$. Every solution in $[0,1]$ of either condition lies in the open interval $(0,1)$.
--
--   The paper's reason: "Because the LHS is decreasing in $z$ and the RHS is increasing in $z$ this has a unique solution." Uniqueness of the roots is what makes the equilibrium candidates of Lemmas 1–3 unique.
--
--   **Formalization Note.** Existence of the root and its interiority rest on the added interiority condition of the model, which says that each left side exceeds $A'$ at $z = 0$ and falls below it at $z = 1$.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), proof of Lemma 2, p. 40 (PDF 42); eqs. (7), (8), pp. 14–15 (PDF 16–17)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem root_unique (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∃! z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 ∧ ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        z ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∃! z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 ∧
        ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1,
        ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z →
        z ∈ Set.Ioo (0 : ℝ) 1 := by sorry

end RatingsAdvert.AdInterval
