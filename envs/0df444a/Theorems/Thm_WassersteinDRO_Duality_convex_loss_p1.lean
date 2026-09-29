-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_convex_loss_p1
-- name    : WassersteinDRO.Duality.convex_loss_p1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T02:20:32.537903+00:00
-- url     : https://prove2.me/theorems/6d62cac5-1c2d-4abe-ad5b-fff5f906d43d
-- title:
--   Theorem 10 — convex loss and $p=1$
-- statement:
--   Assume $\Xi = E$ (the whole space, representing $\mathbb{R}^m$) and that the loss
--   function $\ell$ is convex. If $p=1$ and $\hat P_N$ is the empirical distribution of $N
--   \ge 1$ samples, then the worst-case risk coincides exactly with the Lipschitz-regularized
--   empirical loss,
--   $$R_{\varepsilon,1}(\hat P_N,\ell) = R(\hat P_N,\ell) + \varepsilon\,\mathrm{Lip}(\ell).$$
--   This upgrades Theorem 5's inequality to an exact equality under convexity, $p=1$ and
--   $\Xi = \mathbb{R}^m$.
-- source:
--   Kuhn et al. 2019, Theorem 10, p. 14, citing [61, Theorem 6.3] for the proof

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_nominalRisk
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 10 (Convex loss and p = 1), Kuhn et al. 2019, p. 14: assume `Ξ = R^m` and the
loss function `ℓ(ξ)` is convex. If `p = 1` and `PN` is the empirical distribution, then the
worst-case risk (6) coincides with the Lipschitz-regularized empirical loss,
`Rε,1(PN,ℓ) = R(PN,ℓ) + ε·Lip(ℓ)` — Theorem 5's inequality turned into an exact equality
under convexity, `p = 1` and `Ξ = R^m`. -/
theorem convex_loss_p1 {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (hℓ : Integrable ℓ (empiricalDistribution ξhat)) :
    worstCaseRisk ε 1 Set.univ (empiricalDistribution ξhat) ℓ =
      (nominalRisk (empiricalDistribution ξhat) ℓ : EReal) +
        ((ENNReal.ofReal ε * lipschitzModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.Duality
