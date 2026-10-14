-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_proposition_1_sbm
-- name    : RetailerMarketplace.Entry.proposition_1_sbm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:22.208872+00:00
-- url     : https://prove2.me/theorems/594af542-e42f-4056-93b1-9e8e1f081f72
-- title:
--   Proposition 1.1, p. 5 — SBM: the monopolist alone steers to himself, charges p_M = v and earns v − c
-- statement:
--   Let $c>0$ be the unit cost, $\lambda\in[0,1]$ the share of inattentive consumers, and $v\ge c$ the valuation of a product market supplied by the monopolist $M$ alone (configuration SBM). $M$ chooses a price $p_M$ and a steering choice $S\in\{M,T\}$; inattentive consumers buy from him only if steered to him and $p_M\le v$, attentive consumers buy if $p_M\le v$. Then steering to himself and charging the monopoly price is optimal:
--   $$(p_M,S)=(v,M)\ \text{maximizes } (p_M-c)\,q_M(p_M,S),\qquad\text{with value } \pi_M^{SBM}=v-c.$$
--
--   This is the first case of Proposition 1, which gives $M$'s profit from a nonmarketplace product he enters.
--
--   **Formalization Note** Only $v\ge c$ is assumed (SBM concerns any product, including those $T$ does not enter). The payoff $\pi_M^{SBM}$ is the function `piSBM` of the model file.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 5 (PDF p. 7), Proposition 1, item 1

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model
import Definitions.Def_RetailerMarketplace_Entry_PricingGame

namespace RetailerMarketplace.Entry

/-- Proposition 1.1 (SBM): when only M supplies product `v ≥ c`, steering inattentive consumers to
himself and charging `p_M = v` maximizes his profit, which equals `π_M^SBM = v - c`. -/
theorem proposition_1_sbm (c lam v : ℝ) (hc : 0 < c) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hv : c ≤ v) :
    IsOptSBM c lam v v Steer.M ∧ uM_SBM c lam v v Steer.M = piSBM c v := by sorry

end RetailerMarketplace.Entry
