-- Prove2me | Theorems.Thm_SupplyChainTheory_bullwhip_order_batching
-- name    : SupplyChainTheory.bullwhip_order_batching
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:05:31.925166+00:00
-- url     : https://prove2.me/theorems/cb136b2d-2ac7-43c8-9970-49365facf4fc
-- title:
--   Theorem 13.4: $\mathbb{E}[Q^c] = \mathbb{E}[Q^r] = \mathbb{E}[Q^b] = N\mu$ and $\mathrm{Var}[Q^c] \ge \mathrm{Var}[Q^r] \ge \mathrm{Var}[Q^b] \ge N\sigma^2$
-- statement:
--   **Theorem 13.4.** Let $Q^r_t$, $Q^c_t$ and $Q^b_t$ be the orders received by the supplier in
--   period $t$ under random, positively correlated and balanced ordering respectively, in the
--   batching model of Sect. 13.2.4 with $N \ge 1$ retailers, a reorder interval of $R \ge 1$
--   periods and i.i.d. $N(\mu, \sigma^2)$ demands, the balanced case having $N = MR + k$ with
--   $0 \le k < R$. Then
--
--   1. $\mathbb{E}[Q^c_t] = \mathbb{E}[Q^r_t] = \mathbb{E}[Q^b_t] = N\mu$;
--   2. $\mathrm{Var}[Q^c_t] \ge \mathrm{Var}[Q^r_t] \ge \mathrm{Var}[Q^b_t] \ge N\sigma^2$.
--
--   The orders placed to the supplier have the same mean as the demands placed to the retailers
--   but a larger variance, so order batching produces the bullwhip effect; and correlated ordering
--   produces the largest effect, then random, then balanced. The proof is the three variance
--   formulas together with $N \ge 1$ and $k(R - k) \le N(R - 1)$.
--
--   **Formalization Note** The three ordering patterns are three instances of the batching model
--   with a common $N, R, \mu, \sigma$, each with its own distribution of the number of ordering
--   retailers, given as hypotheses.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 551, Sect. 13.2.4, Theorem 13.4 and its proof

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_order_batching {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {N R : ℕ} {mu sigma : ℝ} (hN : 0 < N) (hR : 0 < R)
    (Br Bc Bb : BatchOrders P N R mu sigma)
    (hXr : ∀ j : ℕ, P.real {ω | Br.X ω = j}
      = (Nat.choose N j : ℝ) * (1 / R) ^ j * (1 - 1 / R) ^ (N - j))
    (hXc0 : P.real {ω | Bc.X ω = 0} = 1 - 1 / R) (hXcN : P.real {ω | Bc.X ω = N} = 1 / R)
    (M k : ℕ) (hk : k < R) (hNMk : N = M * R + k)
    (hXbM : P.real {ω | Bb.X ω = M} = 1 - k / R)
    (hXbM1 : P.real {ω | Bb.X ω = M + 1} = k / R) :
    ((∫ ω, Bc.supplierOrder ω ∂P) = N * mu ∧ (∫ ω, Br.supplierOrder ω ∂P) = N * mu
        ∧ (∫ ω, Bb.supplierOrder ω ∂P) = N * mu)
      ∧ (ProbabilityTheory.variance Br.supplierOrder P
            ≤ ProbabilityTheory.variance Bc.supplierOrder P
          ∧ ProbabilityTheory.variance Bb.supplierOrder P
            ≤ ProbabilityTheory.variance Br.supplierOrder P
          ∧ N * sigma ^ 2 ≤ ProbabilityTheory.variance Bb.supplierOrder P) := by sorry

end SupplyChainTheory
