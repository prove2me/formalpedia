-- Prove2me | Theorems.Thm_RefugeeCash_PDCA_pdca_symmetric_optimal
-- name    : RefugeeCash.PDCA.pdca_symmetric_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:27.028987+00:00
-- url     : https://prove2.me/theorems/190f8869-06bf-4bcf-833b-8312804d1a22
-- title:
--   Proposition 4, symmetric goods (§6.3, eq. (27), p. 22, PDF 23) — under the PDCA scheme the target price p⊙ is an optimal retail price, unique if the target profit exceeds Π0
-- statement:
--   Consider the symmetric-goods model with budget $B > 0$, unit cost $c > 0$ and residents' demand $D$ satisfying Assumption 2, with $\pi_0(p) = (p-c)D(p)$ maximized at $p_0$ and $\Pi_0 = \pi_0(p_0)$. Assume moreover that $\pi_0$ is concave on $(c,\infty)$. Let $(p^\odot,k^\odot)$ be a feasible target:
--   1. $c < p^\odot \le p_0$ and $k^\odot \in [0,1]$;
--   2. the retailer's target profit is at least its pre-arrival maximum, $\Pi(p^\odot,k^\odot) = k^\odot B(1-c/p^\odot) + \pi_0(p^\odot) \ge \Pi_0$.
--
--   Let $k(p) = \min\{(k^\odot + S(p^\odot,k^\odot)(p-p^\odot))^+, 1\}$ be the PDCA scheme (27), so that at price $p$ the retailer earns $\Phi(p) := k(p)B(1-c/p) + \pi_0(p)$. Then
--   1. the scheme pays the target cash fraction at the target price, $k(p^\odot) = k^\odot$;
--   2. $p^\odot$ is an optimal retail price:
--   $$\Phi(p) \le \Phi(p^\odot) \qquad \text{for every price } p > c;$$
--   3. if $\pi_r(p^\odot,k^\odot) + \pi_0(p^\odot) > \Pi_0$, then $p^\odot$ is the unique optimal price: $\Phi(p) = \Phi(p^\odot)$ with $p > c$ forces $p = p^\odot$.
--
--   This is the paper's main design result in the symmetric case: a cash-assistance schedule that falls linearly in the retail price, with the slope (27), makes the target price the retailer's own best choice, with no price regulation.
--
--   **Formalization Note** "Feasible target solution" is read as the retailer clause $\Pi(p^\odot,k^\odot) \ge \Pi_0$ of (26) together with the paper's own form $p^\odot \le p_0$ of the residents' clause $C(p) \ge C(p_0)$ (p. 21), plus $k^\odot \in [0,1]$ and $p^\odot > c$. The refugees' clause $N\,\mathbb E[U] \ge U_0$ of (26) is not assumed, which makes the statement stronger. The page's "if $\pi_0(p)$ is also concave" is read on the price range $(c,\infty)$. Prices range over $p > c$.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), p. 22 (PDF 23), §6.3, eq. (27) and the two paragraphs after it (Proposition 4 for symmetric goods); feasibility (26) and p* ≤ p0, pp. 20–21 (PDF 21–22)

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

namespace RefugeeCash.PDCA

/-- Proposition 4 for symmetric goods, §6.3, p. 22 (PDF 23), eq. (27): if `π0` is concave and the
target `(p⊙, k⊙)` is feasible (`c < p⊙ ≤ p0`, `k⊙ ∈ [0, 1]`, `Π(p⊙, k⊙) ≥ Π0`), then under the PDCA
scheme (27) the retailer is paid `k⊙` at `p⊙`, the price `p⊙` maximizes the retailer's profit
`k(p) B (1 − c/p) + π0(p)` over all prices `p > c`, and it is the unique maximizer when
`πr(p⊙, k⊙) + π0(p⊙) > Π0`. -/
theorem pdca_symmetric_optimal (P : Params) (hP : P.Standing) (pmax p0 : ℝ)
    (hA2 : Assumption2 P pmax p0) (hconc : ConcaveOn ℝ (Set.Ioi P.c) (pi0 P))
    (pT kT : ℝ) (hpT : P.c < pT) (hpT0 : pT ≤ p0) (hkT : kT ∈ Set.Icc (0 : ℝ) 1)
    (hfeas : Pi0 P p0 ≤ retailerProfit P pT kT) :
    kPDCA P pT kT pT = kT ∧
      (∀ p, P.c < p → pdcaProfit P pT kT p ≤ pdcaProfit P pT kT pT) ∧
      (Pi0 P p0 < retailerProfit P pT kT →
        ∀ p, P.c < p → pdcaProfit P pT kT p = pdcaProfit P pT kT pT → p = pT) := by sorry

end RefugeeCash.PDCA
