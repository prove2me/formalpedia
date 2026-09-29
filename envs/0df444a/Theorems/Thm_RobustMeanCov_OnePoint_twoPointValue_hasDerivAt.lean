-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_twoPointValue_hasDerivAt
-- name    : RobustMeanCov.OnePoint.twoPointValue_hasDerivAt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:42:00.700516+00:00
-- url     : https://prove2.me/theorems/d3d8732c-d6e6-4554-b79c-5f6df129d2cb
-- title:
--   (9) — derivative of the two-point objective in $p$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be differentiable, $m,s\in\mathbb R$, and $p\in(0,1)$. Write the two support points of (8) as
--
--   $$
--   a=m-\sqrt{\tfrac{p}{1-p}}\,s,\qquad b=m+\sqrt{\tfrac{1-p}{p}}\,s .
--   $$
--
--   Then $U(p)=p\,u(b)+(1-p)\,u(a)$ is differentiable at $p$ with
--
--   $$
--   \frac{\partial U}{\partial p}(p)=u(b)-u(a)-(b-a)\,\frac{u'(b)+u'(a)}{2}.
--   $$
--
--   This formula is display (9) of the paper. Its sign is the trapezoidal-rule error for $\int_a^b u'$, which is how the convexity or concavity of $u'$ controls the monotonicity of $U(p)$.
--
--   **Formalization Note** The statement is made for every real $s$; the paper's $\sigma_x\ge0$ is a special case.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 102, §3.1, (9)

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue

namespace RobustMeanCov.OnePoint

theorem twoPointValue_hasDerivAt (u : ℝ → ℝ) (hu : Differentiable ℝ u) (m s p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => twoPointValue u m s q)
      (u (m + Real.sqrt ((1 - p) / p) * s) - u (m - Real.sqrt (p / (1 - p)) * s)
        - ((m + Real.sqrt ((1 - p) / p) * s) - (m - Real.sqrt (p / (1 - p)) * s))
          * (deriv u (m + Real.sqrt ((1 - p) / p) * s)
              + deriv u (m - Real.sqrt (p / (1 - p)) * s)) / 2) p := by sorry

end RobustMeanCov.OnePoint
