-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_lemma_6
-- name    : PerishBaseStock.Penalty.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:30.715798+00:00
-- url     : https://prove2.me/theorems/604544ad-0f24-4283-97f6-bf8a9d766f60
-- title:
--   Lemma 6: with bounded demand some optimal policy keeps the order-up-to level at least $\underline S$
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$, zero lead time and FIFO issuance, with costs $h>0$, $p>0$, $\theta\ge0$ and i.i.d. demands with $0<\mathbb E[D]<\infty$. Let $\underline S$ be the least minimizer over $S\ge0$ of
--
--   $$h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\theta S.$$
--
--   Suppose that demand is bounded, $\bar D=\sup\{x:F(x)<1\}<\infty$. Then there is an admissible policy $\pi^{FIFO,*}$ that is optimal, $C^{\pi^{FIFO,*}}=\mathrm{OPT}$, and whose order-up-to level satisfies
--
--   $$x^{\pi^{FIFO,*}}_{t,m}\ge\underline S\qquad\text{for every period }t\ge1\text{ and every demand sample path}.$$
--
--   The lemma gives a uniform floor on the optimal order-up-to level; it is the input to inequality (20) and Proposition 3.
--
--   **Formalization Note** Optimality means exact attainment of the infimum $\mathrm{OPT}$ over all admissible (state-feedback, measurable, time-dependent) policies, not $\varepsilon$-optimality. "Every demand sample path" is taken literally: every sequence in $[0,\infty)^{\mathbb N}$. This is equivalent to the almost-sure reading, since a policy that has the floor almost surely can be modified to order up to at least $\underline S$ in every state without changing its trajectories on those paths. The least minimizer is used because a lower floor is the weaker claim.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 22, Lemma 6; proof in Appendix E.1, pp. ec12–ec13

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Lemma 6: with bounded demand there is an optimal admissible policy whose
order-up-to level is at least `S̲` in every period and on every demand path. -/
theorem lemma_6 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) :
    ∃ π : PerishBaseStock.Lifetime.Policy c.m, policyCost c P π = OPT c P ∧
      ∀ (d : CappedBaseStock.DemandPath) (t : ℕ), (floorLevel c P : ℝ) ≤ totalLevel π d t := by sorry

end PerishBaseStock.Penalty
