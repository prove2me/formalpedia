-- Prove2me | Theorems.Thm_SupplyChainTheory_batch_balanced_ordering
-- name    : SupplyChainTheory.batch_balanced_ordering
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:04:44.245672+00:00
-- url     : https://prove2.me/theorems/a798d946-a766-4dbd-acc8-c05b37a40c90
-- title:
--   Sect. 13.2.4.3: balanced ordering, $\mathrm{Var}[Q^b] = N\sigma^2 + \mu^2k(R-k)$ for $N = MR + k$
-- statement:
--   Suppose the retailers' orders are spread evenly over the $R$-period interval: writing
--   $N = MR + k$ with $0 \le k < R$, $k$ of the $R$ daily groups have $M + 1$ retailers and the
--   other $R - k$ have $M$, so the number of retailers ordering on a given day is $X = M + 1$ with
--   probability $k/R$ and $X = M$ with probability $1 - k/R$. Then the total order $Q^b_t$
--   received by the supplier satisfies
--
--   $$ \mathbb{E}[Q^b_t] = N\mu, \qquad \mathrm{Var}[Q^b_t] = N\sigma^2 + \mu^2 k(R-k) \;\ge\; N\sigma^2, $$
--
--   with equality when $k = 0$, that is when exactly the same number of retailers orders on each
--   day. Balancing is the mildest of the three patterns and is the strategy the book recommends
--   when batching cannot be avoided.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 550-551, Sect. 13.2.4.3 'Balanced Ordering'

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem batch_balanced_ordering {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hR : 0 < R)
    (B : BatchOrders P N R mu sigma) (M k : ℕ) (hk : k < R) (hN : N = M * R + k)
    (hXM : P.real {ω | B.X ω = M} = 1 - k / R)
    (hXM1 : P.real {ω | B.X ω = M + 1} = k / R) :
    (∫ ω, B.supplierOrder ω ∂P) = N * mu
      ∧ ProbabilityTheory.variance B.supplierOrder P
          = N * sigma ^ 2 + mu ^ 2 * k * (R - k) := by sorry

end SupplyChainTheory
