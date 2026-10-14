-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_3
-- name    : ProgCorrMFG.Approx.eq_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:21.288002+00:00
-- url     : https://prove2.me/theorems/6b3fe084-22cd-45d1-8cb9-ae0b3a495109
-- title:
--   (6.3), p. 16 — if player 1 deviates, $\liminf_N J^N_1(\mathfrak m_0^{\otimes N},\gamma^N,\tilde\gamma^N)\ge J(\mathfrak m_0,\rho,\iota)$
-- statement:
--   Assume the hypotheses of Theorem 6.2, and let $\gamma^N=\int\rho_1(\cdot|m)^{\otimes N}\rho_2(dm)$. For every sequence of strategy modifications $\tilde\gamma^N\in\mathcal N^N_{\gamma^N_1}$ of player 1,
--   $$\liminf_{N\to\infty}J_1^N\big(\mathfrak m_0^{\otimes N},\gamma^N,\tilde\gamma^N\big)\ge J(\mathfrak m_0,\rho,\iota).$$
--
--   This is the second half of the proof of Theorem 6.2: asymptotically, no progressive deviation, even with a private randomization device, improves on the mean field cost of following the mediator.
--
--   **Formalization Note** The paper states (6.3) for the near-minimizing sequence of (6.1); here it is stated for every sequence, which is equivalent because the costs are bounded. The $\liminf$ is written as: for every $\delta>0$, eventually $J(\mathfrak m_0,\rho,\iota)-\delta\le J^N_1$. The limit runs along $N=n+2$, for every sequence of realizations and every realization of $(\mathfrak m_0,\rho,\iota)$.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 16, (6.1), (6.3) (proved on pp. 20–25)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_3 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA1 : M.A1) (hA2 : M.A2) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) (hR2 : R2 ρ)
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap)
    (γ' : ∀ n, Measure (ProgN T X G (n + 2 - 1) × ProgN T X G (n + 2 - 1)))
    (hγ' : ∀ n, γ' n ∈ StratModSet ((liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))).map (fun φ => φ 0)))
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (R : ∀ n, NRealization M (n + 2) 0 (Measure.pi fun _ : Fin (n + 2) => m₀)
      (liftSugg (gammaN (ρ.map Prod.snd) ρ₁ (n + 2))) (γ' n) (P n))
    (Ωl : Type) [MeasurableSpace Ωl] (Pl : Measure Ωl) [IsProbabilityMeasure Pl]
    (Rl : MFGRealization M m₀ ρ iotaMFG Pl) :
    ∀ δ > 0, ∀ᶠ n in atTop, Rl.cost - δ ≤ (R n).cost := by sorry

end ProgCorrMFG.Approx
