-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_dual_lower_bound
-- name    : ScenarioReduction.Redistribution.dual_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:48:38.186848+00:00
-- url     : https://prove2.me/theorems/513604f8-0093-48eb-adf7-7c17f98294f3
-- title:
--   Proof of Theorem 2, lower bound: Σ_{i∈J} p_i min_{k∉J} c(ω_i, ω_k) ≤ D(J; q) for every feasible q
-- statement:
--   Under the standing assumptions of Section 3 ($p_i>0$, $\sum_ip_i=1$; $c\ge0$, $c(\omega,\tilde\omega)=0$ iff $\omega=\tilde\omega$, $c$ symmetric), let $J\subsetneq\{1,\dots,N\}$ be a set of deleted scenarios, so that at least one scenario is kept. For every choice of reduced weights $q$ ($q_j\ge0$ for $j\notin J$, $\sum_{j\notin J}q_j=1$),
--
--   $$\sum_{i\in J}p_i\min_{k\notin J}c(\omega_i,\omega_k)\le D(J;q).$$
--
--   Here $D(J;q)$ is the Kantorovich distance between $P=\sum_ip_i\delta_{\omega_i}$ and the reduced measure $\sum_{j\notin J}q_j\delta_{\omega_j}$. The left-hand side does not depend on $q$, so it bounds from below the best distance that any reweighting of the kept scenarios can achieve; it is the lower half of Theorem 2.
--
--   **Formalization Note** The hypothesis that the complement of $J$ is nonempty is implicit on p. 501 (the minimum over $k\notin J$ must range over a nonempty set) and is stated explicitly. The paper's lead-in sentence writes the expression as $\sum_{j\in J}p_j\min_{i\notin J}c_{ij}$, swapping the letters $i$ and $j$; the formalization follows the display that ends the step, which matches (11).
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 501, §3, proof of Theorem 2, lower bound (second paragraph and display)

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset

namespace ScenarioReduction.Redistribution

theorem dual_lower_bound {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (q : Fin N → ℝ) (hq : IsReducedWeight J q) :
    ∑ i ∈ J, p i * minOver Jᶜ (fun k => c (ω i) (ω k)) ≤ transportValue c ω p J q := by sorry

end ScenarioReduction.Redistribution
