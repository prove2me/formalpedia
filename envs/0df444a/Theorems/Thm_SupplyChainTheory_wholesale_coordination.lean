-- Prove2me | Theorems.Thm_SupplyChainTheory_wholesale_coordination
-- name    : SupplyChainTheory.wholesale_coordination
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:26:00.910266+00:00
-- url     : https://prove2.me/theorems/8010295c-02bc-407e-84ca-997817f4168f
-- title:
--   Theorem 14.1 (first part): under the wholesale price contract $Q^*_r = Q^*_s = Q_0$ iff $w = c_s - \frac{c - v}{r - v + p}p_s$
-- statement:
--   **Theorem 14.1, first part.** Under the wholesale price contract with price $w$, the
--   retailer's and supplier's optimal order quantities both coincide with the supply-chain-optimal
--   quantity $Q_0$ if and only if
--
--   $$ w \;=\; c_s - \frac{c - v}{r - v + p}\,p_s. $$
--
--   Coordination is stated as the equality of the sets of maximizers: every maximizer of
--   $\pi_r(\cdot, w)$ is a maximizer of $\Pi$ and conversely, and the same for $\pi_s$. The
--   proof substitutes $w$ into the first-order conditions (14.11)-(14.12) and uses that
--   $S'(Q) = \bar F(Q)$ is strictly decreasing and continuous, so the fractile equations have a
--   common unique solution. This is double marginalization (Spengler 1950): only a price below the
--   supplier's cost aligns the retailer's fractile with the chain's.
--
--   **Formalization Note** $F$ is assumed continuous (an atomless demand law), $p_s > 0$ (the
--   book's proof divides by it), and the chain optimum positive, $\bar F(0) > (c - v)/(r - v + p)$.
--   Strict monotonicity of $F$ is **not** assumed. On all of $\mathbb{R}$ it would exclude every
--   nonnegative demand law, since $F = 0$ on $(-\infty, 0)$, and so the book's own setting. It is not
--   needed either: with the maximizer sets compared as sets, at $w = w^*$ all three sets are
--   $\{Q : \bar F(Q) = (c - v)/(r - v + p)\}$, and for $w \ne w^*$ the retailer's set is disjoint
--   from the chain's, which is nonempty.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 569, Sect. 14.5, Theorem 14.1, Eq. (14.13), and its proof

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_coordination (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D)
    (hps : 0 < P.ps) (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0) (w : ℝ) :
    ((∀ Q, IsMaxOn (retailerProfit P D (wholesaleTransfer w)) Set.univ Q
          ↔ IsMaxOn (chainProfit P D) Set.univ Q)
        ∧ (∀ Q, IsMaxOn (supplierProfit P D (wholesaleTransfer w)) Set.univ Q
          ↔ IsMaxOn (chainProfit P D) Set.univ Q))
      ↔ w = wholesaleCoordPrice P := by sorry

end SupplyChainTheory
