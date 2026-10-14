-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_proposition_5_6
-- name    : ProgCorrMFG.Approx.proposition_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:22.51139+00:00
-- url     : https://prove2.me/theorems/9aa9ad1a-0d06-429f-94c2-0b3f163f8c21
-- title:
--   Proposition 5.6, p. 12 — a closed-loop correlated solution satisfying (R1) is an open-loop correlated solution
-- statement:
--   Assume (A1), and that $\Psi$ is measurable and the costs are measurable and bounded in the measure argument. Let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ be a correlated solution of the mean field game in closed-loop strategies with initial distribution $\mathfrak m_0$ (Definition 4.3). If $\rho$ satisfies (R1), then $\rho$ is also a correlated solution of the mean field game in open-loop strategies (Definition 5.3): for every open-loop policy $u$,
--   $$\hat J(\mathfrak m_0,\rho,u^\iota)\le\hat J(\mathfrak m_0,\rho,u),$$
--   and the consistency condition holds for every realization of $(\mathfrak m_0,\rho,u^\iota)$.
--
--   Enlarging the class of deviations from progressive feedback strategies to open-loop controls with the information structure of Definition 5.1 does not improve the representative player's cost. The proof of (6.3) uses this to compare the limit of the deviating player's costs with $J(\mathfrak m_0,\rho,\iota)$.
--
--   **Formalization Note** Only the first two sentences of the proposition are formalized; the identity of the value functions $\hat V_\varphi=V_\varphi$ is not. The measurability and boundedness of $\Psi$, $f$, $F$ are the conventions under which the costs are defined.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 12, Proposition 5.6 (first two sentences)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG
import Definitions.Def_ProgCorrMFG_Approx_OpenLoop

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem proposition_5_6 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hcost : M.CostsRegular) (hA1 : M.A1)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (hsol : IsCorrelatedSolution M m₀ ρ) (hR1 : R1 ρ) :
    IsOLCorrelatedSolution M m₀ ρ := by sorry

end ProgCorrMFG.Approx
