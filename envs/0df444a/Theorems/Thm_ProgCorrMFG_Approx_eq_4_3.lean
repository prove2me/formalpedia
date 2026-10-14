-- Prove2me | Theorems.Thm_ProgCorrMFG_Approx_eq_4_3
-- name    : ProgCorrMFG.Approx.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:32.383002+00:00
-- url     : https://prove2.me/theorems/f473fd97-d099-4b6e-9e22-1dd48474927b
-- title:
--   §4, p. 7 (4.3) — the MFG cost $J(\mathfrak m_0,\rho,w)$ does not depend on the realization
-- statement:
--   Let $\mathfrak m_0\in\mathcal P(\mathcal X)$, let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ be a correlated suggestion and let $w:\mathcal R\to\widehat{\mathcal R}$ be a strategy modification. Suppose $\Psi$ is Borel measurable and the costs $f$, $F$ are Borel measurable and bounded in the measure argument. Then any two realizations of $(\mathfrak m_0,\rho,w)$ in the sense of Definition 4.1, possibly on different probability spaces, have the same expected cost
--   $$\mathbb E\Big[\sum_{t=0}^{T-1}f\big(t,X_t,\mu_t,w\circ\Phi(t,X^{(t)},\mu^{(t)})\big)+F(X_T,\mu_T)\Big].$$
--
--   This is the fact behind writing the cost as a function $J(\mathfrak m_0,\rho,w)$ of the triple alone, and it justifies stating every comparison of costs in this mission for every realization.
--
--   **Formalization Note** The measurability of $\Psi$ and the measurability and boundedness of the costs are not stated in the paper; they are the conventions under which the expectation is defined.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, p. 7, §4, the sentence introducing (4.3)

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem eq_4_3 {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hcost : M.CostsRegular)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (w : Strat T X G → Prog T X G)
    (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (R₁ : MFGRealization M m₀ ρ w P₁)
    (Ω₂ : Type) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (R₂ : MFGRealization M m₀ ρ w P₂) :
    R₁.cost = R₂.cost := by sorry

end ProgCorrMFG.Approx
