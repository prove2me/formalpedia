-- Prove2me | Theorems.Thm_SatiaLave_Bayes_bayes_return_bounded_by_maxmax_maxmin
-- name    : SatiaLave.Bayes.bayes_return_bounded_by_maxmax_maxmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:45:35.998993+00:00
-- url     : https://prove2.me/theorems/6bbe8781-4c3f-4a1d-9c2c-b4c1088855a4
-- title:
--   Propositions 9 and 10 — αV_i^- + (1−α)min r/(1−β) ≤ f(i, g) ≤ αV_i^+ + (1−α)max r/(1−β)
-- statement:
--   Consider the finite discounted Markovian decision process of Satia and Lave: states $i$, decisions $k \in K_i$, rewards $r^k_{ij}$, discount $0 \le \beta < 1$, and closed convex nonempty sets $S_i^k$ of admissible probability rows $p_i^k$, with $S = \{P : p_i^k \in S_i^k \text{ for all } i, k\}$. Let $f(i,g)$ be the Bayesian optimal return, the bounded solution of the recursive equations (10), and for a prior $g$ let
--   $$
--   \alpha = \operatorname{prob}(P \in S \mid g).
--   $$
--   Let $V^+$ and $V^-$ satisfy the max-max and max-min equations
--   $$
--   V_i^+ = \max_{k \in K_i} \max_{P \in S}\Big\{\sum_j p^k_{ij} r^k_{ij} + \beta \sum_j p^k_{ij} V_j^+\Big\}, \qquad
--   V_i^- = \max_{k} \min_{P \in S}\Big\{\sum_j p^k_{ij} r^k_{ij} + \beta \sum_j p^k_{ij} V_j^-\Big\}.
--   $$
--
--   **Proposition 9.** $f(i,g) \le \alpha V_i^+ + (1-\alpha)\max_{i,j,k}[r^k_{ij}/(1-\beta)]$.
--
--   **Proposition 10.** $f(i,g) \ge \alpha V_i^- + (1-\alpha)\min_{i,j,k}[r^k_{ij}/(1-\beta)]$.
--
--   The theorem asserts both, for every state $i$ and every prior $g$:
--   $$
--   \alpha V_i^- + (1-\alpha)\min_{i,j,k}\frac{r^k_{ij}}{1-\beta} \;\le\; f(i,g) \;\le\; \alpha V_i^+ + (1-\alpha)\max_{i,j,k}\frac{r^k_{ij}}{1-\beta},
--   $$
--   together with the existence of a bounded solution $f$ of (10) and of solutions $V^+$, $V^-$, so that the objects the propositions speak of exist.
--
--   The bounds reduce the intractable Bayesian problem to two finite robust problems (max-max and max-min) plus the single number $\alpha$; they are the bounds used by the paper's implicit-enumeration procedure.
--
--   **Formalization Note** $f$, $V^+$ and $V^-$ are quantified as arbitrary solutions of their equations (bounded, for $f$), with existence asserted in the conclusion; $\alpha$ is computed from $g$. Priors are probability measures on matrices concentrated on transition-probability matrices. The added standing assumptions are $0 \le \beta < 1$, $S_i^k \ne \emptyset$ and at least one state.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 735, Proposition 9; p. 736, Proposition 10

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Propositions 9 and 10: with `α = prob(P ∈ S | g)`,
`α V_i^- + (1 - α) min_{i,j,k} [r^k_{ij}/(1-β)] ≤ f(i, g) ≤ α V_i^+ + (1 - α) max_{i,j,k} [r^k_{ij}/(1-β)]`,
for the bounded solution `f` of (9)/(10) and the solutions `V^+`, `V^-` of the max-max and
max-min equations, all of which exist. -/
theorem bayes_return_bounded_by_maxmax_maxmin {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    (∃ V : S → ℝ, SolvesVplus M V) ∧ (∃ V : S → ℝ, SolvesVminus M V) ∧
    ∀ (f : S → Measure (Mat S D) → ℝ), SolvesEq10 M f → IsBoundedOnPriors f →
    ∀ (Vp Vm : S → ℝ), SolvesVplus M Vp → SolvesVminus M Vm →
    ∀ (g : Measure (Mat S D)), IsPrior g → ∀ i : S,
      alpha M g * Vm i + (1 - alpha M g) * rmin M ≤ f i g ∧
        f i g ≤ alpha M g * Vp i + (1 - alpha M g) * rmax M := by sorry

end SatiaLave.Bayes
