-- Prove2me | Theorems.Thm_SatiaLave_Bayes_prop6_exists_unique_bounded
-- name    : SatiaLave.Bayes.prop6_exists_unique_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:42:55.278074+00:00
-- url     : https://prove2.me/theorems/12a2e604-1dae-4bdc-974e-0c7556d6c7be
-- title:
--   Proposition 6 — the Bayesian recursion (9) has a unique bounded solution f(i, g)
-- statement:
--   Consider the finite discounted Markovian decision process with uncertain transition probabilities of Satia and Lave: states $i$, decisions $k \in K_i$, rewards $r^k_{ij}$, discount $0 \le \beta < 1$. For a prior $g$ on the unknown transition matrix $P$ write $\bar p^k_{ij} = E(p^k_{ij})$ for the prior means and $T^k_{ij} g$ for the posterior after a transition $i \to j$ under decision $k$ (Eq. (8)).
--
--   **Proposition 6** (Martin). There exists a function $f(i, g)$, bounded over all states and priors, that satisfies
--   $$
--   f(i, g) = \max_{k \in K_i} \Big\{ \sum_j \bar p^k_{ij} r^k_{ij} + \beta \sum_j \bar p^k_{ij} f(j, T^k_{ij} g) \Big\} \qquad (10)
--   $$
--   for every state $i$ and prior $g$; and any two bounded solutions of (10) agree at every state and every prior.
--
--   The solution is the Bayesian optimal total expected discounted return, the object that Propositions 8, 9 and 10 bound.
--
--   **Formalization Note** The paper states the result for Eq. (9), $f(i,g) = \max_k\{E(\sum_j p^k_{ij} r^k_{ij}) + \beta\sum_j E[p^k_{ij} f(j, T^k_{ij} g)]\}$. Since $T^k_{ij} g$ does not depend on $P$, linearity of $E$ turns (9) into (10), as the paper itself notes, so (10) is formalized. "Unique" is read as uniqueness at priors: (10) says nothing about $f$ at measures that are not priors, so equality of the whole functions would be false.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 733, Proposition 6 (Eqs. (9), (10))

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proposition 6 (Martin): the recursive equations (9)/(10) have a unique bounded solution
(unique on the set of priors, the only arguments at which (10) constrains `f`). -/
theorem prop6_exists_unique_bounded {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    ∀ f₁ f₂ : S → Measure (Mat S D) → ℝ,
      SolvesEq10 M f₁ → IsBoundedOnPriors f₁ →
      SolvesEq10 M f₂ → IsBoundedOnPriors f₂ →
      ∀ i g, IsPrior g → f₁ i g = f₂ i g := by sorry

end SatiaLave.Bayes
