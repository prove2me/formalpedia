-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_eq_EC_13
-- name    : PerishBaseStock.Penalty.eq_EC_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:32.858456+00:00
-- url     : https://prove2.me/theorems/a3e2b876-7182-4932-b24a-fa0bbdb86871
-- title:
--   (EC.13): with bounded demand, $p\mathbb E[(D-\widetilde S)^+]\le p(\bar D-\widetilde S)\mathbb P(D>\widetilde S)\le(h+\theta)(\bar D-\widetilde S)$
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$ and costs $h>0$, $p>0$, $\theta\ge0$, with i.i.d. demands $D,D_1,D_2,\dots$, $0<\mathbb E[D]<\infty$. Suppose demand is bounded, $\bar D=\sup\{x:F(x)<1\}<\infty$, and let $\widetilde S$ be any minimizer over $[0,\infty)$ of the heuristic cost $\widetilde C$ of (4). Then
--
--   $$p\mathbb E[(D-\widetilde S)^+]\le p(\bar D-\widetilde S)\cdot\mathbb P(D>\widetilde S)\le(h+\theta)(\bar D-\widetilde S).$$
--
--   The estimate controls the lost-sales part of $C(\widetilde S)$ by a quantity that does not grow with $p$; it is the first step of the proof of (26).
--
--   **Formalization Note** The printed chain begins with the identity $p\mathbb E[(D-\widetilde S)^+]=p\mathbb E[(D-\widetilde S)\mathbb 1_{\{D>\widetilde S\}}]$, which is omitted; the two inequalities are stated as a conjunction of real inequalities. $\bar D$ enters as a real number, which is legitimate under the hypothesis $\bar D<\infty$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec6, Appendix B.2, inequality (EC.13)

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Inequality (EC.13): with bounded demand and any minimizer `S̃` of `C̃`,
`p E[(D - S̃)^+] ≤ p (D̄ - S̃) P(D > S̃) ≤ (h + θ)(D̄ - S̃)`. -/
theorem eq_EC_13 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) (S : ℝ≥0) (hS : IsHeuristicLevel c P S) :
    c.p * LostSalesOrderUpTo.Asymptotic.expectedShortfall P.law S ≤
        c.p * ((upperSupport P).toReal - S) * (P.law (Set.Ioi S)).toReal ∧
      c.p * ((upperSupport P).toReal - S) * (P.law (Set.Ioi S)).toReal ≤
        (c.h + c.θ) * ((upperSupport P).toReal - S) := by sorry

end PerishBaseStock.Penalty
