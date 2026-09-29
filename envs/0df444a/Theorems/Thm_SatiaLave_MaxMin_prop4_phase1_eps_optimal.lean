-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_prop4_phase1_eps_optimal
-- name    : SatiaLave.MaxMin.prop4_phase1_eps_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:40:20.764994+00:00
-- url     : https://prove2.me/theorems/12024752-034f-4c71-955f-b8a866c6f65a
-- title:
--   Proposition 4 — Phase 1 finds an $\varepsilon$-optimal policy for nature after finitely many iterations
-- statement:
--   Fix a policy $A$ and let $P^0,P^1,P^2,\dots$ be a run of Phase 1: each $P^{n+1}$ arises from $P^n$ by one Phase 1 iteration. Let $\underline v(A)=\inf_{P\in S}v^A(P)$ be nature's optimum against $A$. Then:
--
--   1. for every $\varepsilon>0$ there is an $n$ such that for all $m\ge n$ and all states $i$,
--   $$v^A_i(P^m)\le \underline v_i(A)+\varepsilon ;$$
--   2. if the stopping test holds at iteration $n$, then $v^A(P^n)=\underline v(A)$ exactly.
--
--   Since $v^A(P^m)\ge\underline v(A)$ always holds, part 1 says that from iteration $n$ on, nature's choice is within $\varepsilon$ of its optimum. Proposition 4 is what licenses Phase 2 to use nature's optimum as the value of $A$.
--
--   **Formalization Note.** "$\varepsilon$-optimal for nature" is read as: nature's return within $\varepsilon$ of nature's optimum $\underline v(A)$, in every state. The paper's proof establishes only that the decreasing sequence of values converges; the Proposition asserts that the limit is nature's optimum, and that is what is stated. Part 2 is an addition, stronger than the printed statement, recording that the routine is exact when its stopping test fires.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 731, Proposition 4 (proof pp. 731-732)

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proposition 4, p. 731: along every run `P 0, P 1, …` of Phase 1 for a policy `A`, for every
`ε > 0` there is an iteration from which on nature's present value is within `ε` of nature's
optimum `robustValue M A` in every state; moreover, if the stopping test fires at an
iteration, nature's choice there is exactly optimal. -/
theorem prop4_phase1_eps_optimal {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : ℕ → Sel M)
    (hrun : ∀ n, IsPhase1Step M A (P n) (P (n + 1))) :
    (∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ i, presentValue M A (P m) i ≤ robustValue M A i + ε) ∧
      ∀ n, Phase1Stops M A (P n) (P (n + 1)) → ∀ i, presentValue M A (P n) i = robustValue M A i := by sorry

end SatiaLave.MaxMin
