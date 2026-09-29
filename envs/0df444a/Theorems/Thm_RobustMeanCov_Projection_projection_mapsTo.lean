-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_projection_mapsTo
-- name    : RobustMeanCov.Projection.projection_mapsTo
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:43:41.993603+00:00
-- url     : https://prove2.me/theorems/49e3c626-89a0-4a9d-a0bf-8557e9a5f988
-- title:
--   The projection $x'\mathbf R$ of $\mathbf R \sim (\mu,\Sigma)$ has mean $x'\mu$ and variance $x'\Sigma x$
-- statement:
--   Let $\mu, x \in \mathbb{R}^n$ and let $\Sigma$ be a real $n\times n$ matrix. If the law $P$ of a random vector $\mathbf R$ belongs to $\mathbb{M}^n_{(\mu,\Sigma)}$, then the law of the scalar $x'\mathbf R$ belongs to the univariate class with mean $\mu_x = x'\mu$ and variance $\sigma_x^2 = x'\Sigma x$:
--
--   $$
--   P \in \mathbb{M}^n_{(\mu,\Sigma)} \;\Longrightarrow\; P\circ (R\mapsto x'R)^{-1} \in \mathbb{M}_{(x'\mu,\; x'\Sigma x)} .
--   $$
--
--   This is the easy half of the general projection property: it gives the lower bound $\min_{\mathbf R\sim(\mu,\Sigma)} E[u(x'\mathbf R)] \ge \min_{\mathbf r\sim(\mu_x,\sigma_x^2)} E[u(\mathbf r)]$ of display (4).
--
--   **Formalization Note** The projected law is the pushforward `P.map (fun R => ⟪x, R⟫)`; the map is continuous, hence measurable, so the pushforward is not the junk zero measure. $x'\Sigma x$ is written `x.ofLp ⬝ᵥ S *ᵥ x.ofLp`. No hypothesis on $\Sigma$ or $x$ is needed.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 100, §2.1, justification of (4)

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- §2.1, justification of (4) (Popescu 2007, p. 100): the projected law of `x′R` has mean
`x′μ` and variance `x′Σx`. -/
theorem projection_mapsTo {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
      (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by sorry

end RobustMeanCov.Projection
