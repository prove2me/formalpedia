-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_fh_of_bounded_costs
-- name    : SennottDP.FiniteHorizon.fh_of_bounded_costs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:40:42.409692+00:00
-- url     : https://prove2.me/theorems/76dceb64-a654-4bf4-8f3e-46e10e36ebad
-- title:
--   Proposition 3.3.1 — bounded costs imply FH(α, n)
-- statement:
--   Let $(\Delta_N)$ be an approximating sequence for the MDC $\Delta$ with countable state space and terminal cost $F$. Assume that there is a finite constant $B$ such that
--   $$
--   C(i,a) \le B \quad\text{and}\quad F(i) \le B \qquad \text{for all states } i \text{ and actions } a \in A_i .
--   $$
--   Then Assumption FH($\alpha$, $n$) holds for all $\alpha \in (0,1]$ and all $n \ge 1$.
--
--   With bounded costs, the approximating sequence method therefore always works for the finite horizon criteria (Theorem 3.2.3).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 45, Proposition 3.3.1

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Proposition 3.3.1 (Sennott, p. 45). Let `(Δ_N)` be an approximating sequence for `Δ`. Assume
that there is a finite constant `B` with `C(i, a) ≤ B` and `F(i) ≤ B` for all state-action pairs.
Then FH(α, n) holds for all `α ∈ (0, 1]` and `n ≥ 1`. -/
theorem fh_of_bounded_costs {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (AS : M.ApproxSeq) (B : ℝ≥0) (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (hF : ∀ i, F i ≤ B) :
    ∀ α : ℝ≥0, 0 < α → α ≤ 1 → ∀ n, 1 ≤ n → AS.FH F α n := by sorry

end SennottDP.FiniteHorizon
