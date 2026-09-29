-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_qbar_upper_bound
-- name    : ScenarioReduction.Redistribution.qbar_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:49:19.621393+00:00
-- url     : https://prove2.me/theorems/ccc7e0cb-7345-4106-beb4-a29e15afdecc
-- title:
--   Proof of Theorem 2, upper bound: q̄ is feasible and D(J; q̄) ≤ Σ_{i∈J} p_i min_{j∉J} c(ω_i, ω_j)
-- statement:
--   Under the standing assumptions of Section 3, let $J\subsetneq\{1,\dots,N\}$ and choose for every deleted index $i\in J$ a kept index $j(i)\notin J$ with $j(i)\in\arg\min_{j\notin J}c(\omega_i,\omega_j)$. Put $J_j=\{i\in J: j(i)=j\}$ and define the optimal redistribution
--
--   $$\bar q_j=p_j+\sum_{i\in J_j}p_i\qquad(j\notin J).$$
--
--   Then $\bar q$ is a feasible reduced weight ($\bar q_j\ge0$ and $\sum_{j\notin J}\bar q_j=1$), and
--
--   $$D(J;\bar q)\le\sum_{i\in J}p_i\min_{j\notin J}c(\omega_i,\omega_j).$$
--
--   Together with the lower bound this shows that $\bar q$ is an optimal reweighting of the kept scenarios: every deleted scenario hands its probability to a nearest kept scenario.
--
--   **Formalization Note** The statement holds for every arg-min selector $j(\cdot)$, not a particular one. The selector's values must be kept indices, because $c(\omega_i,\omega_i)=0$ would make $i$ itself an arg-min over all indices. The complement of $J$ is assumed nonempty (implicit on p. 501).
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 501, §3, proof of Theorem 2, upper bound (definition of η̄ and q̄, and the display D(J; q̄) ≤ …)

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset

namespace ScenarioReduction.Redistribution

theorem qbar_upper_bound {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (jsel : Fin N → Fin N)
    (hsel : IsArgminSelector c ω J jsel) :
    IsReducedWeight J (qbar p J jsel) ∧
      transportValue c ω p J (qbar p J jsel) ≤ ∑ i ∈ J, p i * minOver Jᶜ (fun j => c (ω i) (ω j)) := by sorry

end ScenarioReduction.Redistribution
