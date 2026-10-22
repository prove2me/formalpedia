-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_theorem_6_1
-- name    : SimpleCorrMFG.Conv.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:43.034707+00:00
-- url     : https://prove2.me/theorems/ce6b57d1-bfe0-44f4-955b-9007f98341fe
-- title:
--   Theorem 6.1, p. 19 — limit points of symmetric $\varepsilon_N$-correlated equilibria are correlated mean field game solutions
-- statement:
--   Let $\Psi$ be measurable and $f,F$ bounded measurable, and grant
--   1. (A1) and (A2) for the model;
--   2. (A3) for every $N\ge2$, $\gamma^N$ is a symmetric $\varepsilon_N$-correlated equilibrium in restricted strategies with initial distribution $\mathfrak m^N$, where $\varepsilon_N\ge0$;
--   3. (A4) $\varepsilon_N\to0$;
--   4. (A5) $\mathfrak m^N=\otimes^N\mathfrak m_{0,N}$ with $\mathfrak m_{0,N}\to\mathfrak m_0$ in $\mathcal P(\mathcal X)$.
--
--   For $N\ge2$ let $\rho^N=\mathbb P_N\circ(\Phi_1^N,\mu_1^N(0),\dots,\mu_1^N(T))^{-1}\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$, computed in a realization of $(\mathfrak m^N,\gamma^N,\mathrm{Id})$, where $\mu_1^N(t)=(N-1)^{-1}\sum_{j=2}^N\delta_{X_j^N(t)}$.
--   Then $(\rho^N)_{N\ge2}$ is relatively compact as a subset of $\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$, and every limit point $\rho$ of $(\rho^N)$ is a correlated solution of the mean field game in restricted strategies with initial distribution $\mathfrak m_0$:
--   $$\overline{\{\rho^N:N\ge2\}}\ \text{is compact},\qquad \rho^{N_k}\xrightarrow{\ w\ }\rho\ \Longrightarrow\ \rho\ \text{is a correlated solution (Definition 4.1)}.$$
--
--   The theorem justifies the correlated mean field game as the limit model of $N$-player games with a mediator: symmetric approximate correlated equilibria concentrate on correlated solutions, whose flow of measures may remain random.
--
--   **Formalization Note** $\mathcal P(\cdot)$ carries Mathlib's topology of weak convergence (`ProbabilityMeasure`); relative compactness is compactness of the closure of the range of the sequence $n\mapsto\rho^{n+2}$; a limit point is the limit of a subsequence with strictly increasing indices. Costs, $\rho^N$ and the consistency condition are computed under the canonical product laws of the realizations, which the paper notes do not depend on the realization chosen. Player 1 is index `0`. (A3) is required for $N\ge2$, where the $N$-player game is defined.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 19, Theorem 6.1 (assumptions (A1)–(A5), pp. 17–18; ρ^N, p. 19)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_MFG

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Theorem 6.1 (p. 19). -/
theorem theorem_6_1 {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (hA1 : M.A1) (hA2 : M.A2)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hA3 : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N) ∧ IsEpsCE M (prodInit N (m0N N)) (γ N) (ε N))
    (hA4 : Tendsto ε atTop (𝓝 0))
    (hA5 : Tendsto m0N atTop (𝓝 m₀)) :
    IsCompact (closure (Set.range (rhoSeq M m0N γ))) ∧
      ∀ ρ : ProbabilityMeasure (Strat T X Γ × Flow T X),
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) →
          IsCorrelatedSolution M m₀ ρ := by sorry

end SimpleCorrMFG.Conv
