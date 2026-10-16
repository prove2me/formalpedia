-- Prove2me | Theorems.Thm_PELiquidity_Secondary_proposition_3
-- name    : PELiquidity.Secondary.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:00.378982+00:00
-- url     : https://prove2.me/theorems/29073cef-9b2e-484f-ab20-e5381f2f71cf
-- title:
--   Proposition 3: secondary-market equilibrium thresholds
-- statement:
--   Consider the paper's partnership economy with secondary trading of L-fund claims, Assumption 7, and sufficient L-LP capital at the third threshold. There are strictly ordered thresholds $0<\mu_{H,1}<\mu_{H,2}<\mu_{H,3}<\bar\mu_H$. An equilibrium exists for every capital share $\mu_H\in(0,1)$. H-funds appear only at or above $\mu_{H,3}$; when both types of fund are raised, their promised returns agree.
--
--   For $\mu_H\leq\mu_{H,3}$, only L-funds are raised and
--   $$
--   \bar R_{PE,L}=\frac1{1-\lambda D_L},\qquad
--   D_L=\begin{cases}
--   1-\delta_L,&\mu_H\leq\mu_{H,1},\\
--   \dfrac{I_L-A-\mu_H K}{I_L-A-\lambda\mu_H K},&\mu_{H,1}\leq\mu_H\leq\mu_{H,3}.
--   \end{cases}
--   $$
--   At $\mu_{H,3}$ the discount is $1-\delta_H$. The early call equals $\hat x(\lambda,\delta_L)$ in the first regime and $(1-\lambda)D_L/(1-\lambda D_L)$ between the first two thresholds. From the second through the third threshold it belongs to the optimal interval $[\max\{q/(p+q),(1-\lambda)D_L/(1-\lambda D_L)\},p/(p+q)]$.
--
--   Here $\bar\mu_H K=(pR-\bar f_H)A/(1+r(\lambda,\delta_H)-(pR-\bar f_H))$ with $\bar f_H=p^2B/(p^2-q^2)$, as in (C.3), and Assumption 7 reads $[1+r(\lambda,\delta_H)][1-\lambda+\lambda\delta_H(p+(1-\lambda)q)/((1-\lambda)q)]\geq pR$.
--
--   **Formalization Note** The capacity assumption $A/(1-(pR-\bar f_H))-A\leq K-\delta_H[1+r(\lambda,\delta_H)]\bar\mu_H K$, i.e. $(1-\mu_{H,3})K$ at least Assumption 3's bound with $\mu_{H,3}$ from (C.8), is added because the printed assumptions permit L-LP capital to be scarce below $\mu_{H,3}$, contradicting the printed return formula (e.g. $p=0.9$, $q=0.3$, $R=1.3$, $B=0.3$, $\lambda=0.1$, $\delta_L=0.1$, $\delta_H=0.9$, $A=1$, $K\approx4.97$). The final call is an optimal interval; the printed $x_L=\bar x$ selects one point. Equality of L- and H-fund returns is asserted when both funds are raised, since an unused L-fund price is otherwise unconstrained.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 28, Proposition 3, (22); p. 48, (C.3); p. 51, (C.8)

import Mathlib
import Definitions.Def_PELiquidity_Secondary_Market

namespace PELiquidity.Secondary

theorem proposition_3 (P : PELiquidity.Primary.Params)
    (hA7 : P.p * P.R ≤ PELiquidity.Primary.grossReturn P.lam P.δH *
      (1 - P.lam + P.lam * P.δH *
        (P.p + (1 - P.lam) * P.q) / ((1 - P.lam) * P.q)))
    (hLcap : P.A / (1 - (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) - P.A ≤
      P.K - P.δH * PELiquidity.Primary.grossReturn P.lam P.δH *
        ((P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)) * P.A /
          (PELiquidity.Primary.grossReturn P.lam P.δH -
            (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))))) :
    let muBar := (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)) * P.A /
      ((PELiquidity.Primary.grossReturn P.lam P.δH -
        (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) * P.K)
    ∃ mu₁ mu₂ mu₃ : ℝ,
      0 < mu₁ ∧ mu₁ < mu₂ ∧ mu₂ < mu₃ ∧ mu₃ < muBar ∧
      (∀ muH : ℝ, 0 < muH → muH < 1 →
        ∃ E : AllocationSec, IsEquilibriumSec P muH E) ∧
      (∀ (muH : ℝ) (E : AllocationSec),
        0 < muH → muH < 1 → IsEquilibriumSec P muH E → 0 < E.αH →
          mu₃ ≤ muH ∧ (0 < E.αL → E.RH = E.RL)) ∧
      (∀ (muH : ℝ) (E : AllocationSec),
        0 < muH → muH ≤ mu₃ → IsEquilibriumSec P muH E →
          E.αH = 0 ∧
          E.RL = 1 / (1 - P.lam * discount E) ∧
          (muH ≤ mu₁ → discount E = 1 - P.δL ∧
            E.xL = PELiquidity.Primary.xHat P.lam P.δL) ∧
          (mu₁ ≤ muH →
            discount E = (E.IL - P.A - muH * P.K) /
              (E.IL - P.A - P.lam * muH * P.K)) ∧
          (mu₁ ≤ muH → muH ≤ mu₂ →
            E.xL = (1 - P.lam) * discount E / (1 - P.lam * discount E)) ∧
          (mu₂ ≤ muH →
            max (PELiquidity.Primary.xLow P.p P.q)
              ((1 - P.lam) * discount E / (1 - P.lam * discount E)) ≤ E.xL ∧
            E.xL ≤ PELiquidity.Primary.xBar P.p P.q) ∧
          (muH = mu₃ → discount E = 1 - P.δH)) := by sorry

end PELiquidity.Secondary
