-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_theorem_1
-- name    : SearchDiscovery.Reservation.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:46.789196+00:00
-- url     : https://prove2.me/theorems/06537f06-1b74-4d33-a4bf-e643956d909c
-- title:
--   Theorem 1, p. 13 — taking an available action with the largest purchase, search or discovery value is an optimal policy for the search and discovery problem
-- statement:
--   Consider the search and discovery problem: a consumer with an outside option and possibly some products in the consideration set $C_t$ (valuations $x_j+y_j$ known) and the awareness set $S_t$ (only $x_j$ known) can, in each period, buy a product of $C_t$ and stop, inspect a product of $S_t$ at cost $c_s>0$, or, while possible, discover $n_d$ new products at cost $c_d>0$; with probability $q$ a discovery is the last one. Let $z^s(x)$ be the search value, $Q_s(x,c_s,z^s(x))=0$ for all $x$, (6); $z^b_j=x_j+y_j$ the purchase value, (8); and $z^d$ the discovery value, $Q_d(c_d,c_s,z^d)=0$, (10). Write
--   $$\tilde z^b(t)=\max_{k\in C_t}(x_k+y_k),\qquad \tilde z^s(t)=\max_{k\in S_t}z^s_k\quad(-\infty\text{ if }S_t=\emptyset).$$
--
--   **Theorem.** Let $\pi$ be any policy that, at every information state, follows the three rules
--
--   1. **Stopping rule:** purchase $j\in C_t$ only if $z^b_j=\tilde z^b(t)\ge\max\{\tilde z^s(t),z^d\}$;
--   2. **Inspection rule:** inspect $j\in S_t$ only if $z^s_j=\tilde z^s(t)\ge\max\{\tilde z^b(t),z^d\}$;
--   3. **Discovery rule:** discover only if discovery is available and $z^d\ge\max\{\tilde z^b(t),\tilde z^s(t)\}$,
--
--   where $z^d$ enters the first two rules only while discovery is available. Then, from every initial state, $\pi$ is feasible and optimal:
--   $$V(\Omega_0,A_0;\rho)\le V(\Omega_0,A_0;\pi)\quad\text{for every feasible policy }\rho .$$
--
--   This is the paper's first main result: the optimal policy is myopic, comparing three reservation values, each computed from a one-step comparison with a hypothetical outside option.
--
--   **Formalization Note.** "Characterized by the following three rules" is read as sufficiency: every policy obeying the rules, with any tie-break, is optimal (the converse fails at ties and is not claimed). Rules are imposed at every information state with a nonempty consideration set (it always contains the outside option). The policy's payoff is assumed a.e. strongly measurable (a pathological tie-break could make it non-measurable); its feasibility (a.s. purchase, integrable payoff) is part of the conclusion. Competitors range over all deterministic policies of the information state that are feasible.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 13, Theorem 1

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem theorem_1 (M : SDModel) (hM : M.Standing)
    (zs : ℝ → ℝ) (hzs : ∀ x, M.Qs x (zs x) = 0) (zd : ℝ) (hzd : M.Qd zd = 0)
    (π : InfoState → Act) (hπ : FollowsRules zs zd π)
    (s₀ : InfoState) (hC : s₀.C ≠ [])
    (hπm : AEStronglyMeasurable (M.payoff π s₀) (M.P s₀)) :
    M.Feasible π s₀ ∧
      ∀ ρ : InfoState → Act, M.Feasible ρ s₀ → M.value ρ s₀ ≤ M.value π s₀ := by sorry

end SearchDiscovery.Reservation
