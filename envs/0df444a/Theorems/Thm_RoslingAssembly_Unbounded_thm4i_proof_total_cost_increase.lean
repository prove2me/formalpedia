-- Prove2me | Theorems.Thm_RoslingAssembly_Unbounded_thm4i_proof_total_cost_increase
-- name    : RoslingAssembly.Unbounded.thm4i_proof_total_cost_increase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:29.141634+00:00
-- url     : https://prove2.me/theorems/a437b2d2-a02e-481f-8579-b5d7b5cdfe7a
-- title:
--   Proof of Theorem 4(i), p. 578 — the total cost increase of the one-more-unit policy
-- statement:
--   Consider the assembly model under its standing hypotheses (a tree indexed so that $M_{i-1} \le M_i$; i.i.d. demands $\xi_t \ge 0$ with a density and a finite positive mean; $0 < \alpha < 1$; well-formed initial data $x^0$). Let $i$ be a non-end item, $2 \le i \le N$, let $\delta \ge 0$, and let $\pi$ be a measurable policy, feasible from $x^0$, whose cost (2) is a real number $J$. Let $M_m = \max_{k \in \{i\}\cup B(i)} M_k$. Then the policy $\pi^\delta$ that orders $\delta$ more units of every item $k \in \{i\} \cup B(i)$ in period $M_m - M_k + 1$ and holds them forever has the real cost
--   $$J + \delta\,\alpha^{M_m - M_i}\,\frac{\alpha^{l_i}\Big(h_i + \sum_{k \in B(i)} h_k\,\alpha^{-(M_{s(k)} - M_{s(i)})}\Big)}{1-\alpha}.$$
--
--   The fraction is the paper's "total cost increase", capitalized to period $M_m - M_i + 1$; the factor $\alpha^{M_m - M_i}$ discounts it to period 1, where (2) is valued. Multiplying the condition of Theorem 4(i) by $\alpha^{M_{s(i)}} > 0$ shows that the increase is negative exactly under that condition.
--
--   **Formalization Note.** The paper's argument is for one unit ($\delta = 1$); the cost is linear in $\delta$. The statement is restricted to $i \ge 2$: for the end item $i = 1$ the extra units also change $Y_{1t}$ and hence the backlog term of (2), which the printed display does not account for. The goal theorem still covers $i = 1$. The cost is an extended real; the hypothesis that the cost of $\pi$ is the real number $J$ excludes the $\top - \top$ value.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 578, Appendix B, Proof of Theorem 4 (i), displays 'The additional cost of this policy ...' to 'So, the total cost increase is ... < 0'

import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model
import Definitions.Def_RoslingAssembly_Unbounded_Perturb

namespace RoslingAssembly.Unbounded

open MeasureTheory

/-- Proof of Theorem 4(i), p. 578, "the total cost increase": for a non-end item `i ≥ 2` and a
measurable feasible policy `π` with real cost `J`, the policy with `δ ≥ 0` extra units of the
subsystem `{i} ∪ B(i)` has real cost
`J + δ α^{M_m − M_i} α^{l_i} (h_i + ∑_{k ∈ B(i)} h_k α^{−(M_{s(k)} − M_{s(i)})}) / (1 − α)`,
where `M_m = Mmax i`; the factor `α^{M_m − M_i}` discounts the paper's increase, capitalized to
period `M_m − M_i + 1`, back to period 1. -/
theorem thm4i_proof_total_cost_increase (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ Finset.Icc 2 S.N) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π) (hπ : S.Feasible x0 π)
    (J : ℝ) (hJ : S.cost π = (J : EReal)) :
    S.cost (S.perturb π i δ) =
      ((J + δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i *
          (S.h i + ∑ k ∈ S.B i,
            S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ)))) / (1 - S.α) : ℝ) :
        EReal) := by sorry

end RoslingAssembly.Unbounded
