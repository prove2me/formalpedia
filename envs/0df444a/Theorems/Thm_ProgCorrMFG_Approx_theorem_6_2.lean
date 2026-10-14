-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_theorem_6_2
-- name    : ProgCorrMFG.Approx.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:35.639709+00:00
-- url     : https://prove2.me/theorems/d40c9a7a-a55b-4e05-a6f9-c124b424dc3b
-- title:
--   Theorem 6.2, p. 15 — correlated MFG solutions yield $\varepsilon_N$-correlated equilibria of the $N$-player game, $\varepsilon_N\to0$
-- statement:
--   Let $\mathfrak m_0\in\mathcal P(\mathcal X)$ and suppose (A1)–(A3) hold and $\Psi$ is measurable. Let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ be a correlated solution of the mean field game starting at $\mathfrak m_0$ that satisfies (R1) and (R2), and let $\rho(d\varphi,dm)=\rho_1(d\varphi|m)\rho_2(dm)$ be its disintegration along the flow. For $N\in\mathbb N$ define $\gamma^N\in\mathcal P(\mathcal R^N)$ by
--   $$\gamma^N(C_1\times\cdots\times C_N)=\int_{\mathcal P(\mathcal X)^{T+1}}\prod_{j=1}^N\rho_1(C_j|m)\,\rho_2(dm).$$
--   Then there is a sequence $(\varepsilon_N)\subseteq[0,\infty)$ with $\lim_{N\to\infty}\varepsilon_N=0$ such that, for every $N\ge2$, $\gamma^N$ is an $\varepsilon_N$-correlated equilibrium of the $N$-player game with initial distribution $\mathfrak m_0^{\otimes N}$: for every player $i$ and every strategy modification $\tilde\gamma\in\mathcal N^N_{\gamma^N_i}$,
--   $$J^N_i\big(\mathfrak m_0^{\otimes N},\gamma^N,\iota_{\gamma^N_i}\big)\le J^N_i\big(\mathfrak m_0^{\otimes N},\gamma^N,\tilde\gamma\big)+\varepsilon_N.$$
--
--   The mediator who recommends to the $N$ players conditionally independent copies of the mean field recommendation, all conditioned on one common draw of the flow from $\rho_2$, achieves an approximate correlated equilibrium, robust against deviations that use the whole history of the system and a private randomization device.
--
--   **Formalization Note** $\gamma^N$ is embedded into the progressive strategies of the $N$-player game. The statement is for $N\ge2$, since the empirical measure of the other players needs $N-1\ge1$. A single $\varepsilon_N$ serves every player and every modification, and the inequality holds for every realization of each side.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 15, Theorem 6.2

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem theorem_6_2 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1) (hA2 : M.A2) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) (hR2 : R2 ρ)
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap) :
    ∃ ε : ℕ → ℝ, (∀ N, 0 ≤ ε N) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ N, 2 ≤ N → IsEpsCorrEq M N (ε N) (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ N))
        (Measure.pi fun _ : Fin N => m₀) := by sorry

end ProgCorrMFG.Approx
