-- Prove2me | Theorems.Thm_RatingsAdvert_AdInterval_proposition_1
-- name    : RatingsAdvert.AdInterval.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:56.06436+00:00
-- url     : https://prove2.me/theorems/043650ad-33e8-4e1c-86c6-e947e945ea15
-- title:
--   Proposition 1, p. 15 (PDF 17) — z^R = z^0 > z^AR and p^R_1 = p^0_1 < p^AR_1; p^AR_2 = p^R_2 increasing in q; p^0_2 < p^0_1
-- statement:
--   Consider the two-period model in which a monopolist sells a new product of unknown quality $q \sim U[0,2]$, advertises in period 1 to an interval of size $z \in [0,1]$ that consumers do not observe, and sets prices $p_1$ and $p_2$. Fix parameters $(\tau, \beta, A)$ satisfying the standing assumptions ($0<\tau<1/5$, $0<\beta<1/5$, $A$ twice continuously differentiable with $A(0)=0$, $A'>0$ and $A''>\tau/\beta$ on $[0,1]$, $A''(1)>0.4$) and the interiority condition. Compare three information structures for second-generation consumers: Benchmark (no information), Average Rating (AR) and Reviews.
--
--   1. Each of the three cases has a pure-strategy perfect Bayesian equilibrium.
--   2. For any equilibria $(z^0, p^0_1, p^0_2)$ of the Benchmark case, $(z^R, p^R_1, p^R_2)$ of the Reviews case and $(z^{AR}, p^{AR}_1, p^{AR}_2)$ of the AR case,
--   $$z^R = z^0 > z^{AR}, \qquad p^R_1 = p^0_1 < p^{AR}_1,$$
--   the second-period prices of the Reviews and AR cases coincide at every quality, $p^{AR}_2(q) = p^R_2(q)$ for $q \in [0,2]$, and are strictly increasing in quality on $[0,2]$, and the Benchmark second-period price satisfies $p^0_2 < p^0_1$.
--
--   In words: in period 1 the optimal advertising interval and price are the same in the Benchmark and Reviews cases, while under an average rating the firm advertises to a smaller set of consumers and charges a higher price.
--
--   **Formalization Note.** The Benchmark second-period price is a single number, which encodes "independent of quality". The AR second-period price is a function of the inferred quality $q^e$; on the equilibrium path $q^e = q$, so "the same in the Reviews and AR cases" is the equality of the two pricing rules on $[0,2]$. Existence (item 1) is included so that the comparison is not vacuous; it is the paper's use of "the optimal" interval and price.
-- source:
--   Fainmesser, Lauga & Ofek, Ratings, Reviews, and the Marketing of New Products, authors' manuscript dated September 8, 2020 (Management Science, doi:10.1287/mnsc.2020.3848), p. 15 (PDF 17), Proposition 1; proof p. 38 (PDF 40)

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval

theorem proposition_1 (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∃ z p1 p2 : ℝ, IsPBEBench P z p1 p2) ∧ (∃ (z p1 : ℝ) (p2 : ℝ → ℝ), IsPBERev P z p1 p2) ∧
      (∃ (z p1 : ℝ) (p2 : ℝ → ℝ), IsPBEAR P z p1 p2) ∧
      ∀ (z0 p10 p20 zR p1R : ℝ) (p2R : ℝ → ℝ) (zA p1A : ℝ) (p2A : ℝ → ℝ),
        IsPBEBench P z0 p10 p20 → IsPBERev P zR p1R p2R → IsPBEAR P zA p1A p2A →
        zR = z0 ∧ zA < z0 ∧ p1R = p10 ∧ p10 < p1A ∧
          (∀ q ∈ Set.Icc (0 : ℝ) 2, p2A q = p2R q) ∧ StrictMonoOn p2R (Set.Icc (0 : ℝ) 2) ∧
          p20 < p10 := by sorry

end RatingsAdvert.AdInterval
