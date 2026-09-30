-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_redistribution
-- name    : ScenarioReduction.ForwardSelection.redistribution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:58:08.864357+00:00
-- url     : https://prove2.me/theorems/36300f21-1ac3-4d07-a30e-c945e3e771ab
-- title:
--   Theorem 2.1 — optimal redistribution: $\min_q D(J;q)=D_J$, attained at $\bar q$ of (7)
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be scenarios in a finite-dimensional normed space with probabilities $p_i>0$, $\sum_ip_i=1$, and let $c$ be the cost (3) built from a growth function $h$ and a point $\omega_0$. Let $J\subset\{1,\dots,N\}$ be a set of deleted scenarios with at least one scenario kept. For a reduced weight $q$ ($q_j\ge 0$, $\sum_{j\notin J}q_j=1$) let $D(J;q)$ be the optimal value of the linear transportation problem between $P=\sum_ip_i\delta_{\omega_i}$ and $Q=\sum_{j\notin J}q_j\delta_{\omega_j}$ with cost $c$. Then
--   $$
--   D_J=\min\Bigl\{D(J;q):q_j\ge 0,\ \sum_{j\notin J}q_j=1\Bigr\}=\sum_{i\in J}p_i\min_{j\notin J}c(\omega_i,\omega_j).
--   $$
--   Moreover, for every choice $j(i)\in\arg\min_{j\notin J}c(\omega_i,\omega_j)$ ($i\in J$), the minimum is attained at the redistributed weight
--   $$
--   \bar q_j=p_j+\sum_{i\in J_j}p_i,\qquad J_j=\{i\in J:j(i)=j\},\qquad j\notin J,
--   $$
--   which is itself a reduced weight, and $D(J;\bar q)=D_J$.
--
--   The theorem turns the optimal reduction problem into the combinatorial problem (8) of choosing $J$: once the deleted set is fixed, the best reduced measure moves the mass of each deleted scenario to a nearest kept one.
--
--   **Formalization Note** $D(J;q)$ is the paper's own finite transportation problem (p. 188), not the Kantorovich functional on measures. The first part is stated as: $D_J$ is the least value of the transportation cost over all pairs (reduced weight $q$, feasible plan $\eta$). The second part states that $\bar q$ is a reduced weight and $D_J$ is the least transportation cost over plans with second marginal $\bar q$. The hypothesis that $J$ has nonempty complement is necessary: for $J=\{1,\dots,N\}$ no reduced weight exists.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 190, Theorem 2.1, eqs. (6)–(7)

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsTransportPlan

namespace ScenarioReduction.ForwardSelection

/-- Theorem 2.1 (redistribution), Heitsch–Römisch 2003, p. 190. For the cost (3) and a set `J` of
deleted scenarios with nonempty complement, `D_J` is the minimum of the transportation cost over all
reduced weights `q` and all plans `η` between `P` and `Q`, and the minimum is attained at the
redistributed weight `q̄` of (7), for every choice of nearest kept scenarios `j(i)`. -/
theorem redistribution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    IsLeast {v : ℝ | ∃ q : Fin N → ℝ, ∃ η : Fin N → Fin N → ℝ, IsReducedWeight J q ∧
        IsTransportPlan J p q η ∧ v = transportCost (scenCost h ω₀ ω) J η}
      (reductionCost (scenCost h ω₀ ω) p J hJ) ∧
    ∀ jsel : Fin N → Fin N,
      (∀ i ∈ J, jsel i ∉ J ∧ ∀ j, j ∉ J → scenCost h ω₀ ω i (jsel i) ≤ scenCost h ω₀ ω i j) →
      IsReducedWeight J (redistWeight p J jsel) ∧
      IsLeast {v : ℝ | ∃ η : Fin N → Fin N → ℝ, IsTransportPlan J p (redistWeight p J jsel) η ∧
          v = transportCost (scenCost h ω₀ ω) J η}
        (reductionCost (scenCost h ω₀ ω) p J hJ) := by sorry

end ScenarioReduction.ForwardSelection
