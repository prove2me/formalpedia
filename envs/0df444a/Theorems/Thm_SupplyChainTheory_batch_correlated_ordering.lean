-- Prove2me | Theorems.Thm_SupplyChainTheory_batch_correlated_ordering
-- name    : SupplyChainTheory.batch_correlated_ordering
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:04:09.702581+00:00
-- url     : https://prove2.me/theorems/1757e60f-d1b9-4574-80ef-c0a8fe9d4f93
-- title:
--   Sect. 13.2.4.2: positively correlated ordering, $\mathrm{Var}[Q^c] = N\sigma^2 + \mu^2N^2(R-1)$
-- statement:
--   In the extreme case in which all $N$ retailers order on the same day of the $R$-period
--   interval, the number of retailers ordering on a given day is $X = N$ with probability $1/R$ and
--   $X = 0$ otherwise, and the total order $Q^c_t$ received by the supplier satisfies
--
--   $$ \mathbb{E}[Q^c_t] = N\mu, \qquad \mathrm{Var}[Q^c_t] = N\sigma^2 + \mu^2N^2(R-1) \;\ge\; N\sigma^2. $$
--
--   This is the "hockey stick" of MRP systems taken to its extreme, and it produces the largest
--   variance of the three ordering patterns: the term $\mu^2N^2(R-1)$ grows with the square of the
--   number of retailers, against $\mu^2N(R-1)$ under random ordering.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 549-550, Sect. 13.2.4.2 'Positively Correlated Ordering'

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem batch_correlated_ordering {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hR : 0 < R)
    (B : BatchOrders P N R mu sigma)
    (hX0 : P.real {ω | B.X ω = 0} = 1 - 1 / R) (hXN : P.real {ω | B.X ω = N} = 1 / R) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ ProbabilityTheory.variance B.supplierOrder P
          = N * sigma ^ 2 + mu ^ 2 * (N : ℝ) ^ 2 * (R - 1) := by sorry

end SupplyChainTheory
