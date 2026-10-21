-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_proposition_1
-- name    : StochLoadBal.Makespan.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:10.928167+00:00
-- url     : https://prove2.me/theorems/dccf8b35-9ce9-426a-905f-a5484eab81c7
-- title:
--   Proposition 1, second sentence, corrected — if the LP (5)–(9) with b = 17 is infeasible, every expected makespan exceeds c₀ (polynomial-time solvability not formalized)
-- statement:
--   There is an absolute constant $c_0>0$ with the following property. For every instance of stochastic load balancing on $m\ge1$ unrelated machines (sizes $X_{ij}\ge0$ measurable and integrable, jobs independent), if the linear program (5)–(9) with $b=17$ has no feasible solution, then every assignment $\sigma$ has
--   $$\mathbb E\Big[\max_{i\in[m]}\sum_{j\in J_i}X_{ij}\Big]\ >\ c_0 .$$
--
--   Infeasibility of the LP is the lower-bound certificate of the algorithm: at scale $M$ (sizes divided by $M$) it certifies that the optimal expected makespan exceeds $c_0 M$.
--
--   **Formalization Note** Corrected: the page has $1$ in place of $c_0$, which inherits the error of Lemma 5 (3). The first sentence of the proposition (the LP is solvable in polynomial time) is not formalized; the mission has no model of running time.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 10, Proposition 1 (second sentence)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Proposition 1 (Lower Bound via LP, p. 10), second sentence, corrected: there is an absolute
constant `c₀ > 0` such that, if the LP (5)–(9) with `b = 17` is infeasible, then every
assignment has expected makespan more than `c₀` (the page has `1` in place of `c₀`). -/
theorem proposition_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin m → Fin n → Ω → ℝ),
        (∀ i j, Measurable (X i j)) → (∀ i j ω, 0 ≤ X i j ω) →
        (∀ i j, Integrable (X i j) P) → iIndepFun (fun j ω i => X i j ω) P →
        (¬ ∃ y : Fin m → Fin n → ℝ, LPFeasible P X 17 y) →
        ∀ σ : Fin n → Fin m, c₀ < expMakespan P X σ := by sorry

end StochLoadBal.Makespan
