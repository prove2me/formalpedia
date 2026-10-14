-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_4
-- name    : ProgCorrMFG.Approx.eq_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:16.827516+00:00
-- url     : https://prove2.me/theorems/db793120-2c00-4a3f-9143-fe34e8f1cc20
-- title:
--   (6.4), p. 16 — disintegration of $J^N_1(\mathfrak m_0^{\otimes N},\gamma^N,\iota)$ over $\rho_2$
-- statement:
--   Let $\rho_2$ be a probability measure on $\mathcal P(\mathcal X)^{T+1}$, let $\rho_1(\cdot|m)$ be a probability kernel to $\mathcal R$, let $N\ge2$, and let $\gamma^N=\int\rho_1(\cdot|m)^{\otimes N}\rho_2(dm)$ and $\gamma^N_m=\rho_1(\cdot|m)^{\otimes N}$, both viewed as suggestions in $\mathcal P(\widehat{\mathcal R}_N^N)$. Suppose $\Psi$ is measurable and (A3) holds. Then the cost of player 1 when everybody follows the suggestion disintegrates:
--   $$J_1^N\big(\mathfrak m_0^{\otimes N},\gamma^N,\iota_{\gamma_1^N}\big)=\int_{\mathcal P(\mathcal X)^{T+1}}J_1^N\big(\mathfrak m_0^{\otimes N},\gamma^N_m,\iota_{\gamma^N_{m,1}}\big)\,\rho_2(dm).$$
--
--   This reduces the convergence (6.2) to the case of a deterministic flow $m$, integrated against $\rho_2$.
--
--   **Formalization Note** Costs are costs of realizations. The statement is: for every realization of the left-hand triple and every function $c$ such that, for $\rho_2$-almost every $m$, every realization of $(\mathfrak m_0^{\otimes N},\gamma^N_m,\iota)$ has cost $c(m)$, the left-hand cost equals $\int c\,d\rho_2$.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 16, (6.4)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_4 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ₂ : Measure (Flow T X)) [IsProbabilityMeasure ρ₂]
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (N : ℕ) (hN : 2 ≤ N)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : NRealization M N ⟨0, by omega⟩ (Measure.pi fun _ : Fin N => m₀)
      (liftSugg (gammaN ρ₂ ρ₁ N))
      (iotaN ((liftSugg (gammaN ρ₂ ρ₁ N)).map (fun φ => φ ⟨0, by omega⟩))) P)
    (c : Flow T X → ℝ)
    (hc : ∀ᵐ m ∂ρ₂, ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (R' : NRealization M N ⟨0, by omega⟩ (Measure.pi fun _ : Fin N => m₀)
        (liftSugg (Measure.pi fun _ : Fin N => ρ₁ m))
        (iotaN ((liftSugg (Measure.pi fun _ : Fin N => ρ₁ m)).map (fun φ => φ ⟨0, by omega⟩))) P'),
      R'.cost = c m) :
    R.cost = ∫ m, c m ∂ρ₂ := by sorry

end ProgCorrMFG.Approx
