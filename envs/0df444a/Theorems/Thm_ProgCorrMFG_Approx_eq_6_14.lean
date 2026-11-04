-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_14
-- name    : ProgCorrMFG.Approx.eq_6_14
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T13:34:32.608933+00:00
-- url     : https://prove2.me/theorems/2adf26eb-50b7-48e0-8f29-dcc126ed776e
-- title:
--   (6.14), p. 19 — for $\rho_2$-a.e. flow $m$: $J_1^N(\mathfrak m_0^{\otimes N},\gamma^N_m,\iota)\to J(\mathfrak m_0,\rho_1(\cdot|m)\otimes\delta_m,\iota)$
-- statement:
--   Let $\mathfrak m_0\in\mathcal P(\mathcal X)$, suppose (A1)–(A3) hold and $\Psi$ is measurable, and let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ be a correlated solution of the mean field game starting at $\mathfrak m_0$ that satisfies (R1) and (R2). Let $\rho(d\varphi,dm)=\rho_1(d\varphi|m)\,\rho_2(dm)$ be its disintegration along the flow. For a fixed flow $m\in\mathcal P(\mathcal X)^{T+1}$ and $N\in\mathbb N$, put
--   $$\gamma^N_m:=\rho_1(\cdot|m)^{\otimes N}\in\mathcal P(\mathcal R^N),$$
--   the suggestion under which the $N$ players receive i.i.d. recommendations drawn from $\rho_1(\cdot|m)$.
--
--   Then for $\rho_2$-almost every $m\in\mathcal P(\mathcal X)^{T+1}$,
--   $$\lim_{N\to\infty}J^N_1\big(\mathfrak m_0^{\otimes N},\gamma^N_m,\iota\big)=J\big(\mathfrak m_0,\rho_1(\cdot|m)\otimes\delta_m,\iota\big).$$
--   Here the left side is the cost of player $1$ when all players follow the suggestion. The right side is the mean field cost of a representative player who follows a recommendation drawn from $\rho_1(\cdot|m)$ while the flow is frozen at $m$.
--
--   This is the conditional (fixed-flow) limit established in Steps 1–3 of the proof of (6.2): compactness, propagation of chaos, and the consistency condition of the correlated solution, which identifies the limit flow with $m$ for $\rho_2$-a.e. $m$. Combined with the disintegrations (6.4), (6.5) and dominated convergence, it yields (6.2).
--
--   **Formalization Note** $\gamma^N_m$ is embedded into the progressive strategies of the $N$-player game. The statement is for $N=n+2\ge2$, with player $1$ indexed by `0`. The convergence is asserted for every choice of realizations: an arbitrary sequence of realizations of $(\mathfrak m_0^{\otimes N},\gamma^N_m,\iota)$ and an arbitrary realization of $(\mathfrak m_0,\rho_1(\cdot|m)\otimes\delta_m,\iota)$. The exceptional $\rho_2$-null set does not depend on these choices.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 19, eq. (6.14) (conclusion of Steps 1-3 of the proof of (6.2), pp. 17-19)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_14 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1) (hA2 : M.A2) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) (hR2 : R2 ρ)
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap) :
    ∀ᵐ m ∂(ρ.map Prod.snd),
      ∀ (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
        [∀ n, IsProbabilityMeasure (P n)]
        (R : ∀ n, NRealization M (n + 2) 0 (Measure.pi fun _ : Fin (n + 2) => m₀)
          (liftSugg (Measure.pi fun _ : Fin (n + 2) => ρ₁ m))
          (iotaN ((liftSugg (Measure.pi fun _ : Fin (n + 2) => ρ₁ m)).map (fun φ => φ 0))) (P n))
        (Ωl : Type) [MeasurableSpace Ωl] (Pl : Measure Ωl) [IsProbabilityMeasure Pl]
        (Rl : MFGRealization M m₀ ((ρ₁ m).prod (Measure.dirac m)) iotaMFG Pl),
        Tendsto (fun n => (R n).cost) atTop (𝓝 Rl.cost) := by sorry

end ProgCorrMFG.Approx
