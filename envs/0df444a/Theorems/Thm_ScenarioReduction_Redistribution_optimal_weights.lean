-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_optimal_weights
-- name    : ScenarioReduction.Redistribution.optimal_weights
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:49:41.904985+00:00
-- url     : https://prove2.me/theorems/1e70ab67-0bfc-41f5-a1f7-7d04f8dda935
-- title:
--   Theorem 2 (optimal weights): D_J = min_q D(J; q) = Σ_{i∈J} p_i min_{j∉J} c(ω_i, ω_j), attained by the optimal redistribution rule
-- statement:
--   Let $P=\sum_{i=1}^Np_i\delta_{\omega_i}$ be a discrete probability distribution with scenarios $\omega_i\in\Omega$ and weights $p_i>0$, $\sum_ip_i=1$, and let $c:\Omega\times\Omega\to\mathbb R_+$ satisfy $c(\omega,\tilde\omega)=0$ iff $\omega=\tilde\omega$ and $c(\omega,\tilde\omega)=c(\tilde\omega,\omega)$. For a set $J\subsetneq\{1,\dots,N\}$ of scenarios to be deleted and weights $q_j$ on the kept scenarios, let $D(J;q)$ be the Kantorovich distance (optimal transport cost with cost $c$) between $P$ and $Q=\sum_{j\notin J}q_j\delta_{\omega_j}$. Then
--
--   $$D_J=\min\Big\{D(J;q): q_j\ge0,\ \sum_{j\notin J}q_j=1\Big\}=\sum_{i\in J}p_i\min_{j\notin J}c(\omega_i,\omega_j).$$
--
--   Moreover, the minimum is attained at
--
--   $$\bar q_j=p_j+\sum_{i\in J_j}p_i\quad(j\notin J),\qquad J_j=\{i\in J: j(i)=j\},$$
--
--   for every choice of $j(i)\in\arg\min_{j\notin J}c(\omega_i,\omega_j)$, $i\in J$ (the optimal redistribution rule).
--
--   The theorem gives an explicit formula for the distance between the original distribution and the best reduced distribution on a prescribed set of kept scenarios: the new probability of a kept scenario is its old probability plus the probabilities of all deleted scenarios closest to it. It turns scenario reduction for stochastic programs into the combinatorial problem (13) of choosing $J$.
--
--   **Formalization Note** The statement has three parts: the closed form is the least value of $D(J;q)$ over feasible $q$ (so the minimum is attained); $D_J$, defined as the infimum, equals it; and for every arg-min selector $\bar q$ is feasible and $D(J;\bar q)$ equals it. The hypothesis $J\neq\{1,\dots,N\}$ is implicit in the paper (otherwise (11) has no feasible $q$ and the minimum over $j\notin J$ is empty) and is stated. $J=\emptyset$ is allowed. Measurability of $c$ and conditions (C3), (C4) concern $\Omega\subset\mathbb R^s$ and play no role for finitely supported measures; they are dropped and $\Omega$ is an arbitrary set, which makes the statement more general than the page. $D(J;q)$ is the transportation problem, not the closed form.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 500, Theorem 2, eq. (11); standing assumptions p. 500 (§3 preamble) and p. 498 (C1)–(C2)

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset

namespace ScenarioReduction.Redistribution

theorem optimal_weights {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    IsLeast {x : ℝ | ∃ q : Fin N → ℝ, IsReducedWeight J q ∧ x = transportValue c ω p J q}
        (∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j))) ∧
      optWeightsValue c ω p J = ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) ∧
      ∀ jsel : Fin N → Fin N, IsArgminSelector c ω J jsel →
        IsReducedWeight J (qbar p J jsel) ∧
          transportValue c ω p J (qbar p J jsel) = ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) := by sorry

end ScenarioReduction.Redistribution
