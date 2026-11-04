-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_eq_20
-- name    : PerishBaseStock.Penalty.eq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:24.556614+00:00
-- url     : https://prove2.me/theorems/ade4a07b-8ab2-49ff-9501-ba15fe9f46cf
-- title:
--   (20): a policy with order-up-to floor $\underline S$ outdates at least as much as $\pi_{\underline S}$, pathwise
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$, zero lead time and FIFO issuance, started empty, and let $\underline S$ be the least minimizer over $S\ge0$ of $h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\theta S$. Fix a demand sample path and an admissible policy $\pi$ whose order-up-to level satisfies $x^\pi_{t,m}\ge\underline S$ in every period along that path. Then the cumulative outdated quantity of $\pi$ dominates that of the base-stock policy $\pi_{\underline S}$:
--
--   $$\sum_{t=1}^T o^{\pi}_t\ge\sum_{t=1}^T o^{\pi_{\underline S}}_t,\qquad\forall\,T\ge1.$$
--
--   In the paper the inequality is applied to the optimal policy $\pi^{FIFO,*}$ of Lemma 6; combined with Lemma 1 it yields the lower bound of Proposition 3.
--
--   **Formalization Note** The statement isolates the pathwise content of (20): it is posed for every admissible policy that keeps the floor along the given path, so it does not depend on the existence result of Lemma 6, and optimality of the policy is not used. The paper's period $t$ is Lean period $t-1$, so the sums run over Lean periods $0,\dots,T-1$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 22, inequality (20)

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Inequality (20): along a demand path on which the order-up-to level of `π` never
falls below `S̲`, cumulative outdating under `π` dominates that under `π_S̲`. -/
theorem eq_20 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (π : PerishBaseStock.Lifetime.Policy c.m)
    (d : CappedBaseStock.DemandPath) (hπ : ∀ t : ℕ, (floorLevel c P : ℝ) ≤ totalLevel π d t)
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, outdated (baseStockPolicy c.m (floorLevel c P)) d t ≤
      ∑ t ∈ Finset.range T, outdated π d t := by sorry

end PerishBaseStock.Penalty
