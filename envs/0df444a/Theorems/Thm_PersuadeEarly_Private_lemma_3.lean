-- Prove2me | Theorems.Thm_PersuadeEarly_Private_lemma_3
-- name    : PersuadeEarly.Private.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:10.278316+00:00
-- url     : https://prove2.me/theorems/0684b087-43cb-440b-a27c-a85d705f457a
-- title:
--   Lemma 3, p. 44 — at fixed prices the $(t^*,p_1,p_2)$-mechanism is optimal and earns $\bar D(p_1,p_2)$
-- statement:
--   Under the standing assumptions, fix prices $0\le p_2<p_1$ and let $t^*$ be an optimal solution of (A.16): $t^*$ is feasible and $J(t^*)\ge J(t)$ for every feasible $t$. Then the $(t^*,p_1,p_2)$-mechanism
--   1. is a valid mechanism and is obedient (satisfies (Buy-1)–(No));
--   2. earns revenue $\bar D(p_1,p_2)$;
--   3. earns at least as much as every valid obedient mechanism with the same prices $p_1,p_2$.
--
--   This reduces the firm's problem at fixed prices from an infinite-dimensional design problem to the one-parameter program (A.16).
--
--   **Formalization Note** $p_2<p_1$ is implicit in (A.16) and (B), which divide by $p_1-p_2$. (B) is read with $\min\{\cdot,1\}$, and $\bar D$ includes the no-Buy threshold. The obedience conjunct is the paper's "after observing that the above is feasible in the original problem (i.e. satisfies all the constraints (Buy-1)–(No))".
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 44, Lemma 3; pp. 43–44, (A.16), (A)–(B)

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_AppendixA

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 44, Lemma 3: let `t*` be an optimal solution of (A.16); then, for the pair of prices
`p1, p2`, the `(t*, p1, p2)`-mechanism is an optimal private signaling mechanism.

Stated as: for prices `0 ≤ p2 < p1` and a maximizer `t*` of `J` over the feasible thresholds of
(A.16), the `(t*, p1, p2)`-mechanism is valid and obedient, earns `D̄(p1, p2)`, and earns at least
as much as every valid obedient mechanism with the same prices.

**Formalization Note** `p2 < p1` is implicit in (A.16) and in (B), which divide by `p1 − p2`.
(B) is read with `min{·, 1}`; `D̄` includes the no-Buy threshold (`F̄(t) = 0`). The obedience
conjunct is the paper's "after observing that the above is feasible in the original problem". -/
theorem lemma_3 (M : Model) (hM : M.Standing) :
    ∀ p1 p2 : ℝ, 0 ≤ p2 → p2 < p1 → ∀ tstar, feasible M p1 p2 tstar →
      (∀ t, feasible M p1 p2 t → J M p1 p2 t ≤ J M p1 p2 tstar) →
      (tMech M p1 p2 tstar).Valid ∧ (tMech M p1 p2 tstar).Obedient ∧
        (tMech M p1 p2 tstar).revenue = Dbar M p1 p2 ∧
        ∀ (n : ℕ) (N : Mech M n), N.Valid → N.Obedient → N.p1 = p1 → N.p2 = p2 →
          N.revenue ≤ (tMech M p1 p2 tstar).revenue := by sorry

end PersuadeEarly.Private
