-- Prove2me | Theorems.Thm_SupplyChainTheory_rationing_nash_inflates
-- name    : SupplyChainTheory.rationing_nash_inflates
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:05:56.16375+00:00
-- url     : https://prove2.me/theorems/a2e363e0-9fd5-4b1b-ac39-d3a490f511ff
-- title:
--   Theorem 13.3: in the rationing game both retailers order more than the newsvendor quantity $Q^*$
-- statement:
--   **Theorem 13.3.** Two identical retailers face single-period demand with a continuous,
--   strictly increasing distribution function $F$ on $[0, \infty)$, holding cost $h > 0$ per unit
--   left over and stockout penalty $p > 0$ per lost sale, so that the newsvendor quantity $Q^{*}$
--   satisfies $F(Q^{*}) = p/(h+p)$. The supply is $A_1$ with probability $r$, $0 < r < 1$, and
--   unlimited otherwise, with $0 < A_1 < 2Q^{*}$; a shortage is rationed pro rata to the orders,
--   retailer 1 receiving $A_1Q_1/(Q_1 + Q_2)$. Retailer 1's expected cost is (13.14),
--
--   $$ g_1(Q_1) = (1 - r)\,\mathrm{nv}(Q_1) + r\,\mathrm{nv}\Big(\frac{A_1Q_1}{Q_1 + Q_2}\Big), $$
--
--   with $\mathrm{nv}$ the newsvendor cost. If $Q > 0$ is a symmetric Nash equilibrium, that is
--   $Q$ minimizes $g_1$ over positive order quantities when retailer 2 orders $Q_2 = Q$, then
--
--   $$ Q \;>\; Q^{*}. $$
--
--   In the presence of possible shortages, order quantities are inflated. The book's proof sets the
--   derivative of (13.14) to zero at the symmetric point: the rationed term contributes
--   $rA_1[(h+p)F(A_1/2) - p]/(4Q)$, which is negative because $A_1/2 < Q^{*}$, so the
--   unrationed term must satisfy $(h+p)F(Q) - p > 0$ (Eq. 13.15) against $(h+p)F(Q^{*}) - p = 0$
--   (Eq. 13.16), and $F$ strictly increasing gives $Q > Q^{*}$. The book notes that inflated orders
--   do not by themselves prove inflated variances; the rigorous bullwhip claim for this model is
--   in Rong et al. (2017).
--
--   **Formalization Note** The demand law is a probability measure on $\mathbb{R}$ whose
--   distribution function is continuous and strictly increasing on $[0, \infty)$; the newsvendor
--   loss is assumed integrable. The equilibrium is stated as optimality of $Q$ against every
--   positive $Q_1$ with the other retailer fixed at $Q$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 546-548, Sect. 13.2.3, Theorem 13.3 and its proof, Eq. (13.14)-(13.16); after Lee et al. (1997a)

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem rationing_nash_inflates (h p r A1 Qstar Q : ℝ) (Dlaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dlaw]
    (hh : 0 < h) (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hA : 0 < A1)
    (hint : ∀ y : ℝ, MeasureTheory.Integrable (fun d => h * max (y - d) 0 + p * max (d - y) 0) Dlaw)
    (hFc : Continuous (ProbabilityTheory.cdf Dlaw))
    (hFmono : StrictMonoOn (ProbabilityTheory.cdf Dlaw) (Set.Ici 0))
    (hQs0 : 0 ≤ Qstar) (hQstar : ProbabilityTheory.cdf Dlaw Qstar = p / (h + p))
    (hA2 : A1 < 2 * Qstar) (hQpos : 0 < Q)
    (hNash : ∀ Q1 : ℝ, 0 < Q1 →
      rationingCost h p r A1 Dlaw Q Q ≤ rationingCost h p r A1 Dlaw Q Q1) :
    Qstar < Q := by sorry

end SupplyChainTheory
