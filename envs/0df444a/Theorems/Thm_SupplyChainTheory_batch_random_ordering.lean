-- Prove2me | Theorems.Thm_SupplyChainTheory_batch_random_ordering
-- name    : SupplyChainTheory.batch_random_ordering
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:03:38.855053+00:00
-- url     : https://prove2.me/theorems/b1783a79-3ac1-4b70-bb04-129d241a357c
-- title:
--   Sect. 13.2.4.1: random ordering, $\mathbb{E}[Q^r] = N\mu$ and $\mathrm{Var}[Q^r] = N\sigma^2 + \mu^2N(R-1)$
-- statement:
--   $N$ retailers face i.i.d. $N(\mu, \sigma^2)$ period demands and each orders every $R \ge 1$
--   periods the demand of the previous $R$ periods, on a day chosen uniformly at random from the
--   $R$ days of the interval. The number $X$ of retailers ordering on a given day is then binomial
--   with parameters $N$ and $1/R$, and the total order $Q^r_t$ received by the supplier satisfies
--
--   $$ \mathbb{E}[Q^r_t] = N\mu, \qquad \mathrm{Var}[Q^r_t] = N\sigma^2 + \mu^2 N(R-1) \;\ge\; N\sigma^2. $$
--
--   The book conditions on $X$: given $X$, the order is a sum of $XR$ i.i.d. demands, so
--   $\mathbb{E}[Q \mid X] = XR\mu$ and $\mathrm{Var}[Q \mid X] = XR\sigma^2$, and the variance
--   decomposition $\mathrm{Var}[Q] = \mathbb{E}[\mathrm{Var}[Q\mid X]] + \mathrm{Var}[\mathbb{E}[Q\mid X]]$
--   gives the result. If $R = 1$ the variances coincide, as they should.
--
--   **Formalization Note** The binomial law of $X$ enters as a hypothesis on the probabilities
--   $\Pr[X = j]$, and $Q^r_t$ is `supplierOrder`, the sum over retailers $1, \dots, X$ of their $R$
--   demands.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 549, Sect. 13.2.4.1 'Random Ordering'

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem batch_random_ordering {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hR : 0 < R)
    (B : BatchOrders P N R mu sigma)
    (hX : ∀ j : ℕ, P.real {ω | B.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j)) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ ProbabilityTheory.variance B.supplierOrder P
          = N * sigma ^ 2 + mu ^ 2 * N * (R - 1) := by sorry

end SupplyChainTheory
