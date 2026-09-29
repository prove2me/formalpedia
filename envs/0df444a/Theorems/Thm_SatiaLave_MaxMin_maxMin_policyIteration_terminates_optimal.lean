-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_maxMin_policyIteration_terminates_optimal
-- name    : SatiaLave.MaxMin.maxMin_policyIteration_terminates_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:41:59.109989+00:00
-- url     : https://prove2.me/theorems/67f59507-8247-47e2-ab9e-7e08700d0a65
-- title:
--   Proposition 5 — the max-min policy-iteration algorithm terminates at a max-min optimal policy
-- statement:
--   Let $A^0,A^1,A^2,\dots$ be a run of the max-min policy-iteration algorithm: each $A^{n+1}$ arises from $A^n$ by one Phase 2 iteration (with Phase 1 exact and the retention rule). Write $\underline v(A)=\inf_{P\in S}v^A(P)$ for nature's minimum and $\bar v$ for the max-min return of criterion (2). Then
--
--   1. the max-min returns increase monotonically: $\underline v_i(A^n)\le\underline v_i(A^{n+1})$ for all $n$ and all states $i$;
--   2. there is an iteration $n$, with $n$ smaller than the number of pure stationary policies, at which the algorithm terminates, $A^{n+1}=A^n$, and the policy $A^n$
--      - is max-min optimal: $\underline v_i(A^n)=\bar v_i$ for every state $i$;
--      - attains the solution of the equations (4): $\underline v_j(A^n)=v_j$ for every solution $v$ of (4) and every $j$;
--      - is $\varepsilon$-optimal for every $\varepsilon>0$: $|\underline v_i(A^n)-\bar v_i|\le\varepsilon$.
--
--   The paper states: "The algorithm finds an $\varepsilon$-optimal max-min policy in a finite number of iterations." With Phase 1 exact, the algorithm stops at an exactly optimal policy, which implies the printed $\varepsilon$-optimality for every $\varepsilon$; the paper's $\varepsilon$ reflects only stopping Phase 1 early (Proposition 4). The bound on $n$ is stronger than the printed "finite number of iterations". The optimality of the terminal policy is Proposition 3.
--
--   **Formalization Note.** A run is any sequence of policies related by consecutive Phase 2 steps; such runs exist from every starting policy. Termination is $A^{n+1}=A^n$, the paper's "if the policy changes … return to Phase 1; otherwise, terminate". Phase 2 uses nature's exact minimum as the value of the current policy (the idealization justified by Proposition 4), and keeps $A_i$ on ties (Howard's retention rule), without which the statement is false.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 732, Proposition 5, with p. 731, Proposition 3

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proposition 5, p. 732 (with Proposition 3, p. 731): along every run `A 0, A 1, …` of the
max-min policy-iteration algorithm, the max-min returns increase monotonically, and within
fewer than `|Policy|` iterations the algorithm terminates (`A (n+1) = A n`) at a policy that is
max-min optimal, attains the solution of (4), and is `ε`-optimal for every `ε > 0`. -/
theorem maxMin_policyIteration_terminates_optimal {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : ℕ → Policy S D) (hrun : ∀ n, IsPhase2Step M (A n) (A (n + 1))) :
    (∀ n i, robustValue M (A n) i ≤ robustValue M (A (n + 1)) i) ∧
      ∃ n, n < Fintype.card (Policy S D) ∧ A (n + 1) = A n ∧ IsMaxMinOptimal M (A n) ∧
        (∀ v : S → ℝ, (∀ j, v j = eq4Op M v j) → ∀ j, robustValue M (A n) j = v j) ∧
        ∀ ε > 0, IsEpsMaxMinOptimal M ε (A n) := by sorry

end SatiaLave.MaxMin
