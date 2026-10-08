-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_convex_loss_p1_borel
-- name    : WassersteinDRO.Regularization.convex_loss_p1_borel
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T18:42:45.814168+00:00
-- url     : https://prove2.me/theorems/d58d7d19-a202-486d-8c9a-5855000c0837
-- title:
--   Convex loss and p = 1 over a Borel space
-- statement:
--   Corrected restatement of Kuhn et al. 2019, Theorem 10: assume the loss ℓ is convex on a Borel space E. If p = 1 and P̂_N is the empirical distribution, then the worst-case risk coincides with the Lipschitz-regularized empirical loss: R_{ε,1}(P̂_N,ℓ) = R(P̂_N,ℓ) + ε·Lip(ℓ). The BorelSpace hypothesis is load-bearing: the uncorrected node (arbitrary MeasurableSpace E) is false, because the Wasserstein cost is formalized as a lower integral.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, INFORMS TutORials 2019, Theorem 10, p. 14. Corrected restatement of mission-IV node 302960e5 (WassersteinDRO.Regularization.convex_loss_p1), whose original statement is false as formalized; see triage report triage_wasserstein_dro_reg.md.

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_worstCaseRisk
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- Theorem 10 (Convex loss and p = 1), Kuhn, Mohajerin Esfahani, Nguyen &
Shafieezadeh-Abadeh, INFORMS TutORials 2019, p. 14 — corrected BorelSpace-E
restatement of `WassersteinDRO.Regularization.convex_loss_p1` (302960e5).
The original formalization is FALSE as stated: with an arbitrary
`MeasurableSpace E` (not the Borel one the paper intends) the Wasserstein cost
is a lower integral `∫⁻`, so e.g. E = ℝ with the coarse σ-algebra
{∅, {0}, ℝ\{0\}, ℝ} admits δ₁ in the W₁-ball of radius 0 around δ₀, making
the worst-case risk exceed the Lipschitz-regularized nominal risk (concrete
counterexample: ℓ = |·|, N = 1, ξ̂ 0 = 0, ε = 0 gives LHS ≥ 1 vs RHS = 0).
Adding `[BorelSpace E]` — the paper's intended setting — kills the
lower-integral pathology: a convex ℓ is then continuous, hence
Borel-measurable, and the coupling-cost integral is genuine. -/
theorem convex_loss_p1_borel {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution ξhat) ℓ =
      (nominalRisk (empiricalDistribution ξhat) ℓ : EReal) +
        ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.Regularization
