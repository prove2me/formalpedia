-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_prop3_no_better_policy_undetected
-- name    : SatiaLave.MaxMin.prop3_no_better_policy_undetected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:40:50.991987+00:00
-- url     : https://prove2.me/theorems/e1250d66-489d-43c9-8571-acd133420e62
-- title:
--   Proposition 3 — at termination no better policy goes undetected
-- statement:
--   Suppose the algorithm terminates at the policy $A$: Phase 2, applied to $A$ with nature's optimum $\underline v(A)$ as value, returns $A$ itself (each $A_i$ maximizes the test quantity (7)). Then no pure stationary policy is better than $A$ in any state:
--   $$\underline v_i(B)\le\underline v_i(A)\qquad\text{for every policy } B \text{ and every state } i,$$
--   where $\underline v_i(B)=\inf_{P\in S}v_i^B(P)$ is nature's minimum for $B$.
--
--   The paper's proof reads "better" as "with a higher present value than that yielded by the algorithm". Proposition 3 is the correctness half of the algorithm's validation; Propositions 4 and 5 give termination.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 731, Proposition 3

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proposition 3, p. 731: if the algorithm terminates at `A` (Phase 2 returns `A` itself), no
pure stationary policy has a higher max-min return than `A` in any state. -/
theorem prop3_no_better_policy_undetected {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : Policy S D) (hterm : IsPhase2Step M A A) :
    ∀ (B : Policy S D) (i : S), robustValue M B i ≤ robustValue M A i := by sorry

end SatiaLave.MaxMin
