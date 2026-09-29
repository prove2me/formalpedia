-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_primal_dual_representation
-- name    : ScenarioReduction.Redistribution.primal_dual_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:48:05.80253+00:00
-- url     : https://prove2.me/theorems/1cfbb1a5-6166-4cad-89a7-6806b344f685
-- title:
--   Primal–dual representation of D(J; q): the transportation LP and its dual both attain D(J; q)
-- statement:
--   Let $P=\sum_{i=1}^N p_i\delta_{\omega_i}$ with $p_i>0$ and $\sum_i p_i=1$, let $c:\Omega\times\Omega\to\mathbb R_+$ satisfy $c(\omega,\tilde\omega)=0$ iff $\omega=\tilde\omega$ and $c(\omega,\tilde\omega)=c(\tilde\omega,\omega)$, and write $c_{ij}=c(\omega_i,\omega_j)$. Let $J\subset\{1,\dots,N\}$ and let $q$ be reduced weights: $q_j\ge0$ for $j\notin J$ and $\sum_{j\notin J}q_j=1$. Then the Kantorovich functional $D(J;q)$ of (10) is both the minimum of the transportation problem and the maximum of its dual:
--
--   $$D(J;q)=\min\Big\{\sum_{i,j}c_{ij}\eta_{ij}:\eta_{ij}\ge0,\ \sum_{j\notin J}\eta_{ij}=p_i,\ i\in I,\ \sum_{i=1}^N\eta_{ij}=q_j,\ j\notin J\Big\}=\max\Big\{\sum_{i=1}^Np_iu_i+\sum_{j\notin J}q_jv_j: u_i+v_j\le c_{ij},\ i\in I,\ j\notin J\Big\}.$$
--
--   Both extrema are attained. This is strong duality for a balanced transportation problem, and it is the tool the proof of Theorem 2 uses in both directions: dual feasible points give lower bounds on $D(J;q)$ and primal feasible plans give upper bounds.
--
--   **Formalization Note** The first conjunct says $D(J;q)$ is the least transport cost over feasible plans (so the infimum is attained); the second says it is the greatest dual objective over dual-feasible $(u,v)$, with $u,v$ unrestricted in sign. Only entries $\eta_{ij}$, $v_j$ with $j\notin J$ enter. The standing assumptions of §3 are carried; the measurability, continuity (C3) and growth (C4) conditions on $c$ concern $\Omega\subset\mathbb R^s$ and are dropped, so $\Omega$ is an arbitrary set.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 501, §3, proof of Theorem 2, first display (lead-in at the foot of p. 500); cf. p. 495

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset

namespace ScenarioReduction.Redistribution

theorem primal_dual_representation {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (q : Fin N → ℝ) (hq : IsReducedWeight J q) :
    IsLeast {x : ℝ | ∃ η : Fin N → Fin N → ℝ, IsTransportPlan p J q η ∧ x = transportCost c ω J η}
        (transportValue c ω p J q) ∧
      IsGreatest {x : ℝ | ∃ u v : Fin N → ℝ, IsDualFeasible c ω J u v ∧ x = dualObjective p J q u v}
        (transportValue c ω p J q) := by sorry

end ScenarioReduction.Redistribution
