-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_witness_family_liminf
-- name    : WassersteinDRO.Regularization.witness_family_liminf
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-05T09:55:11.856365+00:00
-- url     : https://prove2.me/theorems/66f1c98f-67cd-4c69-8845-b54ad044b4dc
-- title:
--   Witness family in the epsilon-ambiguity set attains Lipschitz-regularized risk
-- statement:
--   For any lam below the Lipschitz modulus there is a family of measures Q_t in the ε-ambiguity set (eventually in t), each with ℓ integrable, whose nominal risks eventually exceed every level below R_nom + ε·lam.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, INFORMS TutORials 2019 (Theorem 10, Lipschitz regularization of Wasserstein DRO); decomposition leaves of WassersteinDRO.Regularization.convex_loss_p1_borel (d58d7d19-a202-486d-8c9a-5855000c0837).

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_ambiguitySet
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Regularization

theorem witness_family_liminf {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E]
    (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hm : Measurable ℓ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hP : Integrable ℓ (empiricalDistribution ξhat))
    (lam : ℝ) (hlam : 0 < lam) (hlt : ENNReal.ofReal lam < lipschitzModulus ℓ) :
    ∃ Q : ℝ → Measure E, ∃ T₀ : ℝ,
      (∀ t : ℝ, T₀ ≤ t → Q t ∈ ambiguitySet ε 1 Set.univ (empiricalDistribution ξhat)) ∧
      (∀ t : ℝ, T₀ ≤ t → Integrable ℓ (Q t)) ∧
      ∀ r : ℝ, r < nominalRisk (empiricalDistribution ξhat) ℓ + ε * lam →
        Filter.Eventually (fun t => r < nominalRisk (Q t) ℓ) Filter.atTop := by sorry
end WassersteinDRO.Regularization
