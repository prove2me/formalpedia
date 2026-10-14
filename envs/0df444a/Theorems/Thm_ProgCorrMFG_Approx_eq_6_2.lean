-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_2
-- name    : ProgCorrMFG.Approx.eq_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:22.743173+00:00
-- url     : https://prove2.me/theorems/2c42de88-8f8d-4e17-8b39-09484daf302f
-- title:
--   (6.2), p. 16 — if nobody deviates, $J^N_1(\mathfrak m_0^{\otimes N},\gamma^N,\iota)\to J(\mathfrak m_0,\rho,\iota)$
-- statement:
--   Assume the hypotheses of Theorem 6.2: $\Psi$ is measurable, (A1)–(A3) hold, $\rho$ is a correlated solution of the mean field game with initial distribution $\mathfrak m_0$ satisfying (R1)–(R2), and $\rho(d\varphi,dm)=\rho_1(d\varphi|m)\rho_2(dm)$. Let $\gamma^N=\int\rho_1(\cdot|m)^{\otimes N}\rho_2(dm)$. Then
--   $$\lim_{N\to\infty}J_1^N\big(\mathfrak m_0^{\otimes N},\gamma^N,\iota_{\gamma_1^N}\big)=J(\mathfrak m_0,\rho,\iota).$$
--
--   This is the first half of the proof of Theorem 6.2: when every player follows the mediator, the cost of a player converges to the mean field cost.
--
--   **Formalization Note** The limit is taken along $N=n+2$, $n\to\infty$. Both costs are costs of realizations: for every sequence of realizations of $(\mathfrak m_0^{\otimes N},\gamma^N,\iota)$ for player 1 and every realization of $(\mathfrak m_0,\rho,\iota)$, the first costs converge to the second.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 16, (6.2) (proved on pp. 16–19)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_2 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1) (hA2 : M.A2) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) (hR2 : R2 ρ)
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap)
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (R : ∀ n, NRealization M (n + 2) 0 (Measure.pi fun _ : Fin (n + 2) => m₀)
      (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))) (iotaN ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))).map (fun φ => φ 0))) (P n))
    (Ωl : Type) [MeasurableSpace Ωl] (Pl : Measure Ωl) [IsProbabilityMeasure Pl]
    (Rl : MFGRealization M m₀ ρ iotaMFG Pl) :
    Tendsto (fun n => (R n).cost) atTop (𝓝 Rl.cost) := by sorry

end ProgCorrMFG.Approx
