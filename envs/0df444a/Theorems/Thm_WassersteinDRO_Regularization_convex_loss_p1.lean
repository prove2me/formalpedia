-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_convex_loss_p1
-- name    : WassersteinDRO.Regularization.convex_loss_p1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T02:41:28.261734+00:00
-- url     : https://prove2.me/theorems/302960e5-c4aa-4db2-8f3c-040204d01d67
-- title:
--   Theorem 10 — Convex loss and p = 1
-- statement:
--   Assume $\Xi = \mathbb{R}^m$ and the loss function $\ell(\xi)$ is convex. If $p=1$ and
--   $\hat P_N$ is the empirical distribution, then the worst-case risk coincides with the
--   Lipschitz-regularized empirical loss: $R_{\varepsilon,1}(\hat P_N,\ell) = R(\hat P_N,\ell) +
--   \varepsilon \cdot \mathrm{Lip}(\ell)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Theorem 10, p. 14

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_worstCaseRisk
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- Theorem 10 (Convex loss and p = 1), Kuhn et al. 2019, p. 14: assume `Ξ = R^m` and the
loss function `ℓ(ξ)` is convex. If `p = 1` and `PN` is the empirical distribution, then the
worst-case risk (6) coincides with the Lipschitz-regularized empirical loss,
`Rε,1(PN,ℓ) = R(PN,ℓ) + ε·Lip(ℓ)`. Redefined locally in this chapter's own namespace
(matching `01-duality`'s statement of the same theorem); see
`Def_WassersteinDRO_Regularization_wassersteinDistance` for why. -/
theorem convex_loss_p1 {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution ξhat) ℓ =
      (nominalRisk (empiricalDistribution ξhat) ℓ : EReal) +
        ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.Regularization
