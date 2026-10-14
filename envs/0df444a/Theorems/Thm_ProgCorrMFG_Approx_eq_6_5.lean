-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_6_5
-- name    : ProgCorrMFG.Approx.eq_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:17.647186+00:00
-- url     : https://prove2.me/theorems/e5365023-4c18-46ff-9b1d-2707c78523b0
-- title:
--   (6.5), p. 17 — disintegration of $J(\mathfrak m_0,\rho,\iota)$ over $\rho_2$
-- statement:
--   Let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ with second marginal $\rho_2$, and let $\rho_1(\cdot|m)$ be a probability kernel with $\rho(d\varphi,dm)=\rho_1(d\varphi|m)\rho_2(dm)$. Suppose $\Psi$ is measurable and (A3) holds. Then
--   $$J(\mathfrak m_0,\rho,\iota)=\int_{\mathcal P(\mathcal X)^{T+1}}J\big(\mathfrak m_0,\rho_1(\cdot|m)\otimes\delta_m,\iota\big)\,\rho_2(dm).$$
--
--   The mean field cost under the identity modification is the average, over the flow, of the cost for the deterministic flow $m$ with suggestion law $\rho_1(\cdot|m)$.
--
--   **Formalization Note** Costs are costs of realizations, as in (6.4): for every realization of $(\mathfrak m_0,\rho,\iota)$ and every $c$ such that, for $\rho_2$-a.e. $m$, every realization of $(\mathfrak m_0,\rho_1(\cdot|m)\otimes\delta_m,\iota)$ has cost $c(m)$, the cost equals $\int c\,d\rho_2$.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 17, (6.5)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_6_5 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : MFGRealization M m₀ ρ iotaMFG P)
    (c : Flow T X → ℝ)
    (hc : ∀ᵐ m ∂(ρ.map Prod.snd), ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (R' : MFGRealization M m₀ ((ρ₁ m).prod (Measure.dirac m)) iotaMFG P'),
      R'.cost = c m) :
    R.cost = ∫ m, c m ∂(ρ.map Prod.snd) := by sorry

end ProgCorrMFG.Approx
