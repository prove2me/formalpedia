-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_phase2_step_improves
-- name    : SatiaLave.MaxMin.phase2_step_improves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:41:34.426352+00:00
-- url     : https://prove2.me/theorems/ef99f083-b04a-4a87-b73c-3182ed1d17fe
-- title:
--   Proof of Proposition 5 — each policy change strictly improves the max-min return
-- statement:
--   Let $B$ be obtained from $A$ by one Phase 2 iteration (with the retention rule: $B_i=A_i$ whenever $A_i$ maximizes the test quantity (7)). If $B\ne A$, then
--   $$\underline v_i(B)\ge\underline v_i(A)\quad\text{for all } i=1,\dots,N,\qquad\text{and the strict inequality holds for at least one } i,$$
--   where $\underline v(\cdot)$ is nature's minimum.
--
--   The paper: "We first show that each iteration of the algorithm results in an improved policy for the decision maker. … Therefore, $v_i^B\ge v_i^A$ for all $i=1,\dots,N$, and the strict inequality holds for at least one $i$." Since there are finitely many policies, this is what makes the algorithm terminate.
--
--   **Formalization Note.** The strict inequality depends on the retention rule, which is not printed but is the rule of Howard's policy iteration (see the definition `Algorithm`).
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 732, Proof of Proposition 5

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proof of Proposition 5, p. 732: if Phase 2 changes the policy from `A` to `B ≠ A`, the
max-min return of `B` is at least that of `A` in every state and strictly larger in at least
one. -/
theorem phase2_step_improves {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A B : Policy S D) (hstep : IsPhase2Step M A B) (hne : B ≠ A) :
    (∀ i, robustValue M A i ≤ robustValue M B i) ∧ ∃ i, robustValue M A i < robustValue M B i := by sorry

end SatiaLave.MaxMin
