-- Prove2me | Theorems.Thm_SupplyChainTheory_buyback_allocation
-- name    : SupplyChainTheory.buyback_allocation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:31:32.061558+00:00
-- url     : https://prove2.me/theorems/7c89c6cf-5a87-40c5-b826-2ff69b167a37
-- title:
--   Theorem 14.5: under the buyback contract with $w(b)$ the profits are monotone in $b$ and any division of $\Pi(Q_0)$ is attainable, with the five cases at $b_1 < b_2$
-- statement:
--   **Theorem 14.5.** Under the buyback contract with the wholesale price $w(b)$ of (14.22),
--   evaluated at the chain-optimal quantity $Q_0$, the retailer's profit is decreasing and the
--   supplier's increasing in $b \in [0, r - v + p_r]$. Moreover, with
--
--   $$ b_1 = r - v + p_r - (r - v + p)\frac{\Pi(Q_0) + \mu p_r}{\Pi(Q_0) + \mu p}, \qquad
--      b_2 = r - v + p_r - (r - v + p)\frac{\mu p_r}{\Pi(Q_0) + \mu p}, $$
--
--   one has $0 < b_1 < b_2 < r - v + p_r$, and:
--
--   1. if $0 \le b < b_1$, the supplier earns negative profit and the retailer more than $\Pi(Q_0)$;
--   2. if $b = b_1$, the retailer earns the entire supply chain profit;
--   3. if $b_1 < b < b_2$, the profits are shared, both being positive;
--   4. if $b = b_2$, the supplier earns the entire supply chain profit;
--   5. if $b_2 < b \le r - v + p_r$, the retailer earns negative profit and the supplier more than $\Pi(Q_0)$.
--
--   Together with Theorem 14.4 this makes buyback a coordinating contract: for some $b$ both
--   players earn positive profit at $Q_0$, and any division of $\Pi(Q_0)$ between them can be
--   reached by choosing $b$. The proof is the affine identities (14.27)-(14.28) with $\lambda$
--   decreasing in $b$, and the bound $\Pi(Q_0) \le \mu(r - c) < \mu(r - v)$ for $b_1 > 0$.
--
--   **Formalization Note** $b_1 < b_2$ requires $\Pi(Q_0) > 0$, which the book's proof attributes to
--   $v < r$ but which is a separate assumption (a chain whose optimal expected profit is not
--   positive has nothing to share); it is a hypothesis here, together with $\mu > 0$.
--
--   Both goodwill costs are also assumed positive, $p_s > 0$ and $p_r > 0$. The book's standing
--   data allow either to be $0$, and then the printed strict inequalities fail: at $p_s = 0$,
--   $p = p_r$ and $b_1 = 0$ exactly, and at $p_r = 0$, $b_2 = r - v + p_r$ exactly. The book's step
--   $\frac{\mu(r-v) + \mu p_r}{\mu(r-v) + \mu p} > \frac{\Pi(Q_0) + \mu p_r}{\Pi(Q_0) + \mu p}$ is strict
--   only when $p_r < p$, i.e. $p_s > 0$. Its own examples have $p_s = p_r = 0.2$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 577, Sect. 14.6, Theorem 14.5 and its proof, Eq. (14.29)-(14.32)

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem buyback_allocation (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (hmu : 0 < meanDemand D)
    (hps : 0 < P.ps) (hpr : 0 < P.pr)
    (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) (hpos : 0 < chainProfit P D Q0) :
    let πr := fun b => retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let πs := fun b => supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let b1 := buybackB1 P D Q0
    let b2 := buybackB2 P D Q0
    StrictAntiOn πr (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ StrictMonoOn πs (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ 0 < b1 ∧ b1 < b2 ∧ b2 < P.r - P.v + P.pr
      ∧ (∀ b, 0 ≤ b → b < b1 → πs b < 0 ∧ chainProfit P D Q0 < πr b)
      ∧ πr b1 = chainProfit P D Q0
      ∧ (∀ b, b1 < b → b < b2 → 0 < πr b ∧ 0 < πs b)
      ∧ πs b2 = chainProfit P D Q0
      ∧ (∀ b, b2 < b → b ≤ P.r - P.v + P.pr → πr b < 0 ∧ chainProfit P D Q0 < πs b) := by sorry

end SupplyChainTheory
