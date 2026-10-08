-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_prop2_pure_stationary_optimal
-- name    : SatiaLave.MaxMin.prop2_pure_stationary_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:38:57.872677+00:00
-- url     : https://prove2.me/theorems/d2703525-4971-47e3-a0ac-3f79412eeb92
-- title:
--   Proposition 2 — a pure stationary policy is optimal
-- statement:
--   There is a pure stationary policy $A$ such that, for every solution $v$ of the equations (4) (which allow the decision maker randomized decisions and nature mixed choices), nature's minimum for $A$ equals $v$ in every state:
--   $$\inf_{P\in S} v^A_j(P)=v_j\qquad\text{for every state } j;$$
--   moreover $A$ is max-min optimal among pure stationary policies.
--
--   The paper's gloss (p. 730): nature need not use a mixed strategy, since it sees the decision maker's decision before making its own, and the decision maker, knowing nature's pure strategy, has no reason to use a mixed one. Together with Proposition 1 this says that a single pure stationary policy attains the max-min return simultaneously in all states.
--
--   **Formalization Note.** "Optimal" is read as attaining the solution of (4), the randomized max-min value, in every state at once; the conjunct `IsMaxMinOptimal` adds optimality among pure stationary policies. The proof is cited from Satia's thesis.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 730, Proposition 2

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4

namespace SatiaLave.MaxMin

/-- Proposition 2, p. 730: some pure stationary policy `A` attains, in every state at once, the
solution of the equations (4) (which allow randomized decisions and mixed choices of nature);
in particular `A` is max-min optimal among pure stationary policies. -/
theorem prop2_pure_stationary_optimal {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    ∃ A : Policy S D, (∀ v : S → ℝ, (∀ j, v j = eq4Op M v j) → ∀ j, robustValue M A j = v j) ∧
      IsMaxMinOptimal M A := by sorry

end SatiaLave.MaxMin
