-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tight_opt
-- name    : RevenueOrdered.Tightness.tight_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:22.805577+00:00
-- url     : https://prove2.me/theorems/94dbcee9-1f5a-4c66-8555-7511749213cb
-- title:
--   Theorem 3.4 proof, p. 10 — offering $\{(i,i)\}$ earns $k$, and $\mathrm{OPT}=k$
-- statement:
--   In the tight instance with $0<\varepsilon\le\tfrac12$, offering the products $(i,i)$ for $i\in[k]$ yields revenue $k$, and this is optimal:
--   $$
--   \mathrm{rev}\big(\{(i,i): i\in[k]\}\big)=k=\mathrm{OPT}.
--   $$
--
--   The paper states the optimality in a parenthesis ("in fact, this is the optimal solution") without proof.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- The optimum of the tight instance (p. 10): offering the products `(i, i)`, `i ∈ [k]`, yields
revenue `k`, and this is optimal, `OPT = k`. -/
theorem tight_opt (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    rev (tightP k ε) (tightRevenue k ε) (diagonalSet k) = k ∧
      RevenueOrdered.Ratio.opt (tightP k ε) (tightRevenue k ε) = k := by sorry

end RevenueOrdered.Tightness
