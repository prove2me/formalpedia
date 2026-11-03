-- Prove2me | Theorems.Thm_WeaklyCoupledDP_proposition_3_1
-- name    : WeaklyCoupledDP.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:07.980675+00:00
-- url     : https://prove2.me/theorems/41133812-9492-43ec-85ae-0982d0d541e9
-- title:
--   Proposition 3.1 — the ALP is an upper bound, $V^*_1(s_1,e_1) \le V^{\mathrm{LP}}_1(s_1,e_1)$
-- statement:
--   Let $V^*$ be the optimal value function of the weakly coupled DP (2). For every feasible solution $V = (V_{t,i})$ of the approximate linear program (5),
--   $$
--   V^*_1(s_1,e_1) \le \sum_{i=1}^N V_{1,i}(s_{1,i},e_1).
--   $$
--   In particular the optimal value of the ALP satisfies $V^*_1(s_1,e_1) \le V^{\mathrm{LP}}_1(s_1,e_1)$: the ALP relaxation is an upper bound on the optimal expected total reward.
--
--   This is the first link in the chain $V^* \le V^{\mathrm{LP}} \le V^{\lambda*}$ that the paper studies.
--
--   Differences from the source:
--   - generalization: V*₁(s₁,e₁) ≤ V^LP₁(s₁,e₁), the ALP optimum → the bound for every ALP-feasible V; reason: it does not presuppose that the ALP optimum exists, and applied to an optimal V it is the printed statement.
--   - reading: V* is the value of the policy problem (1), which satisfies (2) → V* is defined by the recursion (2); reason: the paper states that (2) expresses the optimal value function (p.4).
--   - reading: (5b) uses V_{T+1,i} without a value → ALP feasibility includes V_{T+1,i} = 0; reason: the convention V_{T+1} = 0 of (2) and (7); without it the ALP is unbounded below.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), Proposition 3.1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_optimalValue
import Definitions.Def_WeaklyCoupledDP_Model_ALPFeasible

namespace WeaklyCoupledDP

/-- **Proposition 3.1** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), p.6):
`V*₁(s₁, e₁) ≤ V^LP₁(s₁, e₁)`.

**Formalization Note.** `V^LP₁(s₁, e₁)` is the optimal value of the ALP (5); the bound is stated for
every ALP-feasible `V`, which does not presuppose that the optimum exists. `V*` is the value of
the DP (2). -/
theorem proposition_3_1 {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*}
    {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)
    (V : M.ValueArray) (hV : M.ALPFeasible V) :
    M.optimalValue 1 M.s₁ M.e₁ ≤ M.alpObjective V := by sorry

end WeaklyCoupledDP
