-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_eq_6
-- name    : VehicleSharePricing.Static.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:12.43654+00:00
-- url     : https://prove2.me/theorems/2b18c411-4c5b-4c89-8099-f96655f549d7
-- title:
--   Equation (6), p. 9 — the recursion at $K-i+1$ and $0\le\alpha(K-i)\le(K-i)/(N+K-i-1)$
-- statement:
--   Let $q$ be a quantile policy with balanced flows that induces a strongly connected network, with workload $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}$, let $r$ be a positive solution of the traffic equations (9), and let $\alpha(\cdot)$ be the availability at a location $l$. Then for every $K$ and every $i=1,2,\dots,K$:
--
--   1. the recursion holds at $K-i+1$:
--   $$\alpha(K-i+1)=\frac{K-i+1}{N+K-i+\frac{\lambda}{\mu}\bigl[1-\alpha(K-i)\bigr]};\qquad(6)$$
--   2. $0\le\alpha(K-i)$;
--   3. $\alpha(K-i)\,(N+K-i-1)\le K-i$, i.e. $\alpha(K-i)\le\dfrac{K-i}{N+K-i-1}$ whenever the denominator is positive.
--
--   These are the two facts that the proof of Theorem 2 iterates.
--
--   **Formalization Note** The upper bound is written multiplied out: when $N=1$ and $i=K$ the paper's quotient is $0/0$. Since $1\le i\le K$, the natural-number difference $K-i$ is exact. Posed for every balanced quantile policy inducing a strongly connected network, which includes $q^s$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 9, proof of Theorem 2, Equation (6) and the bounds after it

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability

namespace VehicleSharePricing.Static

/-- Equation (6) and the bounds that follow it, proof of Theorem 2, p. 9: under a quantile
policy `q` with balanced flows that induces a strongly connected network, with `λ/μ` its
workload, for every `i = 1, …, K` and every location `l`,
`α(K − i + 1) = (K − i + 1) / (N + K − i + (λ/μ)[1 − α(K − i)])` and
`0 ≤ α(K − i) ≤ (K − i)/(N + K − i − 1)`, the upper bound written as
`α(K − i) (N + K − i − 1) ≤ K − i`. -/
theorem eq_6 {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K i : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K) (l : L) :
    availability P q r (K - i + 1) l =
        ((K - i : ℕ) + 1 : ℝ) / ((Fintype.card L : ℝ) + ((K - i : ℕ) : ℝ) +
          workload P q * (1 - availability P q r (K - i) l)) ∧
      0 ≤ availability P q r (K - i) l ∧
      availability P q r (K - i) l * ((Fintype.card L : ℝ) + ((K - i : ℕ) : ℝ) - 1) ≤
        ((K - i : ℕ) : ℝ) := by sorry

end VehicleSharePricing.Static
