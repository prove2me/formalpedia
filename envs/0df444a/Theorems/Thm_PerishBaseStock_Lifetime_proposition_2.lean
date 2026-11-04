-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_proposition_2
-- name    : PerishBaseStock.Lifetime.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:47.525035+00:00
-- url     : https://prove2.me/theorems/a28ea642-7069-427d-a517-02ba17b176a2
-- title:
--   Proposition 2 — $\mathrm{OPT}\ge\widetilde C(\widetilde S)$
-- statement:
--   Consider the perishable lost-sales inventory system with lifetime $m\ge 1$, zero lead time and FIFO issuance, with costs $h>0$, $p>0$, $\theta\ge 0$. Let $\widetilde S$ be a minimizer of the heuristic cost $\widetilde C$ of (4) over $[0,+\infty)$. Then the optimal long-run average cost over all admissible policies satisfies
--   $$\mathrm{OPT}\;\ge\;\widetilde C(\widetilde S)=\min_{S\ge 0}\widetilde C(S).$$
--
--   This lower bound on the optimal cost is used in the proofs of Theorems 1 to 6 of the paper; combined with an upper bound on $C(\widetilde S)$ it bounds the optimality gap of the heuristic base-stock policy.
--
--   **Formalization Note** The paper states Proposition 2 under any issuance policy; only the FIFO system is formalized here. $\mathrm{OPT}$ is an infimum over all admissible (measurable, state-feedback, time-dependent) policies, in $[0,\infty]$; $\widetilde C(\widetilde S)\ge 0$ is embedded with `ENNReal.ofReal`.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 21, Proposition 2

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem proposition_2 (P : CappedBaseStock.DemandLaw) (c : Params) (Stilde : ℝ≥0)
    (hS : IsHeuristicLevel P c Stilde) :
    ENNReal.ofReal (heuristicCost P c Stilde) ≤ OPT P c := by sorry

end PerishBaseStock.Lifetime
