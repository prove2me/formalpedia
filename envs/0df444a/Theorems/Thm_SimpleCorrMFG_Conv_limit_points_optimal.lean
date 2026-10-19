-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_limit_points_optimal
-- name    : SimpleCorrMFG.Conv.limit_points_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:28.540998+00:00
-- url     : https://prove2.me/theorems/e09abaaa-bc5d-4270-a02c-81a860579457
-- title:
--   Proof of Theorem 6.1, Steps One–Three, pp. 19–23 — every limit point of $(\rho^N)$ satisfies the optimality condition
-- statement:
--   Let $\Psi$ be measurable and $f,F$ bounded measurable, and grant
--   1. (A1) and (A2) for the model;
--   2. (A3) for every $N\ge2$, $\gamma^N$ is a symmetric $\varepsilon_N$-correlated equilibrium in restricted strategies with initial distribution $\mathfrak m^N$, where $\varepsilon_N\ge0$;
--   3. (A4) $\varepsilon_N\to0$;
--   4. (A5) $\mathfrak m^N=\otimes^N\mathfrak m_{0,N}$ with $\mathfrak m_{0,N}\to\mathfrak m_0$ in $\mathcal P(\mathcal X)$.
--
--   For $N\ge2$ let $\rho^N=\mathbb P_N\circ(\Phi_1^N,\mu_1^N(0),\dots,\mu_1^N(T))^{-1}\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$, computed in a realization of $(\mathfrak m^N,\gamma^N,\mathrm{Id})$, where $\mu_1^N(t)=(N-1)^{-1}\sum_{j=2}^N\delta_{X_j^N(t)}$.
--   Let $\rho$ be a limit point of $(\rho^N)_{N\ge2}$ in the topology of weak convergence. Then for every strategy modification $u:\mathcal R\to\mathcal R$,
--   $$J(\mathfrak m_0;\rho,\mathrm{Id})\le J(\mathfrak m_0;\rho,u),$$
--   that is, $\rho$ satisfies the optimality condition (i) of Definition 4.1.
--
--   This is the first half of the identification of limit points in Theorem 6.1: no unilateral modification of the mediator's recommendation improves the representative player's cost in the limit.
--
--   **Formalization Note** A limit point is the weak limit of a subsequence $(\rho^{N_k})$ with $N_k$ strictly increasing; the $n$-th term of the sequence is $\rho^{n+2}$. Costs are computed under the canonical law.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 19–23 (proof of Theorem 6.1, Steps One–Three; conclusion on p. 23)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_MFG

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Proof of Theorem 6.1, Steps One–Three (pp. 19–23): every limit point of `(ρ^N)` satisfies the
optimality condition of Definition 4.1. -/
theorem limit_points_optimal {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (hA1 : M.A1) (hA2 : M.A2)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hA3 : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N) ∧ IsEpsCE M (prodInit N (m0N N)) (γ N) (ε N))
    (hA4 : Tendsto ε atTop (𝓝 0))
    (hA5 : Tendsto m0N atTop (𝓝 m₀))
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X))
    (hρ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) :
    IsOptimal M m₀ ρ := by sorry

end SimpleCorrMFG.Conv
