-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_proposition_1
-- name    : SolarNonOwn.BizChoice.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:14.276695+00:00
-- url     : https://prove2.me/theorems/e55d2d97-cedc-43d3-82ad-a103d4aeabcb
-- title:
--   Proposition 1, p. 15 — optimal business-model offers, with threshold boundaries excluded
-- statement:
--   A monopolist solar power company chooses sales, lease, and PPA prices to maximize profit $\Pi$ from customers' actual minimum-cost choices. Let $c$ be the normalized panel cost, $C_0$ the sales-only profitability limit, and $A_2=\beta/(\beta+r)$ the investment-subsidy threshold. Under the standing assumptions, cost thresholds depend only on the model parameters and are uniform over admissible demand distributions and $c$. A global maximizer exists for every $0<c<C_0$, and every global maximizer has these offer sets:
--
--   $$\begin{array}{c|ccc}\alpha<A_2 & c<C_1: \{P,S\} & C_1<c<C_2: \{P,L,S\} & C_2<c: \{L,S\}\\ A_2\le\alpha & c<C_3: \{P,S\} & C_3<c: \{S\} & \end{array}$$
--
--   Here an offer means positive customer adoption, $P$ is a power purchase agreement, $L$ is leasing, and $S$ is sales. The first case allows $C_1=C_2$, so the all-three interval can be empty.
--
--   **Formalization Note** The printed proposition assigns an offer set at equality with $C_1,C_2,C_3$ although its proof has degenerate or tied optima there; these equality points are excluded. The thresholds are existential before the demand law and cost vary because one printed formula refers to a root that is absent in some subsidy cases. The model uses the disclosed tie rule at $p=r$, assumes $c>0$, and maximizes over all real price triples. The proof's nonnegative-adoption constraints hold automatically for actual choice sets.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. 15, Proposition 1; pp. OA7–OA8 (PDF pp. 39–40), proof and threshold conventions

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

/-- Proposition 1, p. 15, corrected at threshold costs as explained in the paper notes.
The thresholds depend on the model parameters, uniformly over admissible demand laws
and panel costs. -/
theorem proposition_1 (prm : Params) (hs : Standing prm) :
    (prm.alpha < A2 prm →
      ∃ C1 C2 : ℝ, C1 ≤ C2 ∧
        ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
        ∀ c : ℝ, 0 < c → c < C0 prm →
        (∃ x : Prices, IsMaxOn (profit prm h c) Set.univ x) ∧
        ∀ x : Prices, IsMaxOn (profit prm h c) Set.univ x →
          (c < C1 → offers prm h x = ({BizOpt.P, BizOpt.S} : Finset BizOpt)) ∧
          (C1 < c → c < C2 → offers prm h x = ({BizOpt.P, BizOpt.L, BizOpt.S} : Finset BizOpt)) ∧
          (C2 < c → offers prm h x = ({BizOpt.L, BizOpt.S} : Finset BizOpt))) ∧
    (A2 prm ≤ prm.alpha →
      ∃ C3 : ℝ,
        ∀ (h : Measure ℝ) [IsProbabilityMeasure h], h (Set.Iic 0) = 0 →
        ∀ c : ℝ, 0 < c → c < C0 prm →
        (∃ x : Prices, IsMaxOn (profit prm h c) Set.univ x) ∧
        ∀ x : Prices, IsMaxOn (profit prm h c) Set.univ x →
          (c < C3 → offers prm h x = ({BizOpt.P, BizOpt.S} : Finset BizOpt)) ∧
          (C3 < c → offers prm h x = ({BizOpt.S} : Finset BizOpt))) := by sorry

end SolarNonOwn.BizChoice
