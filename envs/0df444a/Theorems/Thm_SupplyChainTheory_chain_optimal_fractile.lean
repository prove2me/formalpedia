-- Prove2me | Theorems.Thm_SupplyChainTheory_chain_optimal_fractile
-- name    : SupplyChainTheory.chain_optimal_fractile
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:25:33.371375+00:00
-- url     : https://prove2.me/theorems/4463f0a1-4b87-4222-99fe-539e3c447166
-- title:
--   Eq. (14.8): $Q_0$ maximizes the chain profit iff $\bar F(Q_0) = (c - v)/(r - v + p)$, and such a $Q_0$ exists
-- statement:
--   For a demand law with finite mean and continuous distribution function $F$, the total supply
--   chain profit $\Pi(Q) = (r - v + p)S(Q) - (c - v)Q - p\mu$ is maximized exactly at the order
--   quantities $Q_0$ with
--
--   $$ \bar F(Q_0) \;=\; \frac{c - v}{r - v + p}, $$
--
--   and at least one such $Q_0$ exists. This is (14.8): $S'(Q) = \bar F(Q)$ by (14.2), $\Pi$ is
--   concave, and its stationary points are its maximizers. The book identifies it with the
--   newsvendor critical fractile for the chain acting as one newsvendor with cost $c$, price $r$,
--   penalty $p$ and salvage $v$. The fractile lies strictly between $0$ and $1$ because
--   $v < c < r$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 567-568, Sect. 14.4, Eq. (14.7)-(14.8) and the concavity remark 'Q0 is a maximizer, not a minimizer'

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem chain_optimal_fractile (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q ↔ 1 - ProbabilityTheory.cdf D Q = (P.c - P.v) / (P.r - P.v + P.p))
      ∧ ∃ Q0, IsMaxOn (chainProfit P D) Set.univ Q0 := by sorry

end SupplyChainTheory
