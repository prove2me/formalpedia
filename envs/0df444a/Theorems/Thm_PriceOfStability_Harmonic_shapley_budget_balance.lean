-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_shapley_budget_balance
-- name    : PriceOfStability.Harmonic.shapley_budget_balance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:39:57.357657+00:00
-- url     : https://prove2.me/theorems/c6ef1f71-4369-4872-84c7-1c5818fb4ab7
-- title:
--   Sect. 1 — Shapley cost shares exactly pay for the designed network
-- statement:
--   Consider the fair (Shapley) cost-sharing game on players $1,\dots,k$ and a finite edge set $E$, where the cost $c_e(x_e)$ of an edge used by $x_e$ players is split equally among them. For every strategy vector $S=(S_1,\dots,S_k)$, the players' payments add up to the cost of the designed network:
--   $$\sum_{i=1}^k C_i(S_1,\dots,S_k)=\sum_{e\in\bigcup_i S_i} c_e(x_e).$$
--
--   This budget-balance property identifies the social cost $\sum_i C_i$ with the cost of the network, so bounds stated for either apply to the other.
--
--   **Formalization Note.** The paper states it for constant costs $c_e$; the statement here allows load-dependent costs $c_e(x)$ (constant costs are the special case) and every strategy vector, feasible or not.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1603 (PDF p. 2), Sect. 1, unnumbered display

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Sect. 1, p. 1603 (PDF p. 2), unnumbered display: the Shapley cost shares completely pay
for the designed network, `Σᵢ Cᵢ(S₁, …, S_k) = Σ_{e ∈ ∪ᵢ Sᵢ} c_e`.

**Formalization Note.** Stated for load-dependent edge costs `c_e(x)` (constant costs are
`c e x = c_e`) and for every strategy vector, feasible or not: the identity uses neither. -/
theorem shapley_budget_balance {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) (S : ι → Finset E) :
    sumCost (fairGame strategies c) S = designCost c S := by sorry

end PriceOfStability.Harmonic
