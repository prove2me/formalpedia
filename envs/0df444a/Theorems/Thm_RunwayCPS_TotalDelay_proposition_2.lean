-- Prove2me | Theorems.Thm_RunwayCPS_TotalDelay_proposition_2
-- name    : RunwayCPS.TotalDelay.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:51.373689+00:00
-- url     : https://prove2.me/theorems/3e845b2c-defb-4aef-9df9-1b3c838b3cf1
-- title:
--   Proposition 2 — in a minimum-total-delay schedule, consecutive aircraft are separated by exactly the minimum separation
-- statement:
--   Consider the runway problem of §5.2 without time windows: $n$ aircraft, maximum position shift $k$, precedence pairs, and separations $\delta_{ab}\ge0$ satisfying the triangle inequality
--   $$\delta_{ac}\le\delta_{ab}+\delta_{bc}\qquad\text{for all aircraft }a,b,c.$$
--   Let $(\sigma,t)$ be a feasible schedule (a $k$-CPS sequence respecting the precedence pairs, landing times $t_p\ge0$, and $t_q-t_p\ge\delta_{\sigma(p)\sigma(q)}$ for all positions $p<q$) whose total delay $t_1+\dots+t_n$ is minimal among all feasible schedules. Then every aircraft is separated from its predecessor by exactly the minimum required separation:
--   $$t_p-t_{p-1}=\delta_{\sigma(p-1)\sigma(p)}\qquad\text{for every position }p=2,\dots,n .$$
--
--   This is the structural fact behind the shortest-path formulation of §5.2: once the sequence is fixed, an optimal schedule has no slack between consecutive aircraft. As the paper notes, it fails in the presence of time windows.
--
--   **Formalization Note** Positions are 0-based `Fin n`; the conclusion is stated for every pair of positions $q,p$ with $q+1=p$. The proposition does not claim that the first aircraft lands at time $0$, and neither does the statement. Nonnegative separations and the triangle inequality are the paper's standing assumptions for arrivals-only or departures-only operations (§2, p. 1652).
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1656, Proposition 2

import Mathlib
import Definitions.Def_RunwayCPS_TotalDelay_Network

namespace RunwayCPS.TotalDelay

theorem proposition_2 {n : ℕ} (I : Instance n)
    (hδ : ∀ a b : Fin n, 0 ≤ I.δ a b)
    (htri : ∀ a b c : Fin n, I.δ a c ≤ I.δ a b + I.δ b c)
    (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) (hfeas : IsFeasible I σ t)
    (hopt : ∀ (σ' : Equiv.Perm (Fin n)) (t' : Fin n → ℝ), IsFeasible I σ' t' →
      totalDelay t ≤ totalDelay t') :
    ∀ (p q : Fin n), (q : ℕ) + 1 = (p : ℕ) → t p - t q = I.δ (σ q) (σ p) := by sorry

end RunwayCPS.TotalDelay
