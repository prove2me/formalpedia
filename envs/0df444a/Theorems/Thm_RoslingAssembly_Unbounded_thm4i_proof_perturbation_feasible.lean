-- Prove2me | Theorems.Thm_RoslingAssembly_Unbounded_thm4i_proof_perturbation_feasible
-- name    : RoslingAssembly.Unbounded.thm4i_proof_perturbation_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:20.806003+00:00
-- url     : https://prove2.me/theorems/524658b7-4fd0-4f3b-b231-1e31a0a49104
-- title:
--   Proof of Theorem 4(i), p. 578 — ordering δ more units of {i} ∪ B(i) and holding them forever keeps the policy feasible
-- statement:
--   Consider the assembly model under its standing hypotheses: a tree with $N \ge 1$ items indexed so that $M_{i-1} \le M_i$; demands $\xi_t \ge 0$ independent with a common law that has a density and a finite positive mean; a discount factor $0 < \alpha < 1$; and well-formed initial data $x^0$.
--
--   Let $i$ be an item, $\delta \ge 0$, and $\pi$ a measurable policy that is feasible from $x^0$, i.e. satisfies (3) almost surely in every period. Then the policy $\pi^\delta$, which orders $\delta$ more units of every item $k \in \{i\} \cup B(i)$ in period $M_m - M_k + 1$ and holds them in stock forever, is again measurable and feasible from $x^0$:
--   $$X^{\delta}_{kt} \le Y^{\delta}_{kt} \le X^{l,\delta}_{jt} \qquad \text{for all } k,\ t \text{ and } j \in P(k), \text{ almost surely.}$$
--
--   The proof of Theorem 4(i) uses this implicitly: the alternative policy it compares with must itself be admissible for Problem P.
--
--   **Formalization Note.** The standing hypotheses are carried for uniformity with the goal, although the statement needs only the tree structure. Feasibility is almost sure.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 578, Appendix B, Proof of Theorem 4 (i), first three sentences ('Consider the subsystem ... held in stock forever.')

import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model
import Definitions.Def_RoslingAssembly_Unbounded_Perturb

namespace RoslingAssembly.Unbounded

open MeasureTheory

/-- Proof of Theorem 4(i), p. 578: ordering `δ ≥ 0` more units of every item of the subsystem
`{i} ∪ B(i)`, timed so that each extra unit arrives when its successor orders its own extra unit,
and holding them forever, preserves measurability and feasibility (3). -/
theorem thm4i_proof_perturbation_feasible (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π) (hπ : S.Feasible x0 π) :
    IsMeasurablePolicy (S.perturb π i δ) ∧ S.Feasible x0 (S.perturb π i δ) := by sorry

end RoslingAssembly.Unbounded
