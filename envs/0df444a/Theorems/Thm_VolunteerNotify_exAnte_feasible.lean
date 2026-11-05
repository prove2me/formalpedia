-- Prove2me | Theorems.Thm_VolunteerNotify_exAnte_feasible
-- name    : VolunteerNotify.exAnte_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:47.680198+00:00
-- url     : https://prove2.me/theorems/418e782c-53ac-4cd4-85f3-d648e8cc0b31
-- title:
--   §4.1, pp.12–14 — every candidate, and $x^*$ of (5), lies in $\mathcal P$
-- statement:
--   Each candidate for the ex ante solution is feasible for (LP):
--
--   1. every optimal solution $x^*_{LP}$ of (LP) lies in $\mathcal P$;
--   2. for every $m\ge1$, every output $x^*_{AA}$ of the Frank–Wolfe variant lies in $\mathcal P$, being an average of feasible solutions;
--   3. every solution $x^*_{SQ}$ of the programs (SQ-$v$) lies in $\mathcal P$;
--   4. consequently every $x^*$ of (5) lies in $\mathcal P$.
--
--   Feasibility is the hypothesis under which Lemma 3 applies to $x^*$.
--
--   Differences from the source:
--   - generalization: x* is the argmax of f over the three candidates of (5) → `IsExAnte`: every value of (5) over any optimizer of (LP), any m ≥ 1 and Frank–Wolfe run, any solution of (SQ-v), and any tie-break; reason: the candidates are not unique; each run of the source is one such value
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, §4.1, p.12 ("x* ∈ P") and p.13 (Frank–Wolfe output is feasible)

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte

namespace VolunteerNotify

/-- Feasibility of the ex ante solution, Manshadi–Rodilitz, arXiv:2002.08474v7, pp.12–14: each
candidate `x*_LP`, `x*_AA`, `x*_SQ`, and so `x*` of (5), lies in `P`. -/
theorem exAnte_feasible {V S T : ℕ} (I : Instance V S T) :
    (∀ x, IsLPSolution I x → x ∈ feasibleSet I) ∧
    (∀ (m : ℕ) (x : Decision V S T), 1 ≤ m → IsFrankWolfeOutput I m x → x ∈ feasibleSet I) ∧
    (∀ x, IsSQSolution I x → x ∈ feasibleSet I) ∧
    (∀ x, IsExAnte I x → x ∈ feasibleSet I) := by sorry

end VolunteerNotify
