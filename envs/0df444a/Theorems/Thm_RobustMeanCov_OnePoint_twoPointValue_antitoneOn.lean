-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_twoPointValue_antitoneOn
-- name    : RobustMeanCov.OnePoint.twoPointValue_antitoneOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:42:41.827159+00:00
-- url     : https://prove2.me/theorems/fc929e98-d810-4335-b122-4ce38fa624c6
-- title:
--   Proof of Proposition 7 — convex $u'$ makes $U(p,x)$ nonincreasing in $p$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be differentiable with convex derivative $u'$, let $m\in\mathbb R$ and $s>0$. Then the two-point objective
--
--   $$
--   p\ \longmapsto\ U(p)=p\,u\!\Big(m+\sqrt{\tfrac{1-p}{p}}\,s\Big)+(1-p)\,u\!\Big(m-\sqrt{\tfrac{p}{1-p}}\,s\Big)
--   $$
--
--   is nonincreasing on $(0,1)$.
--
--   Consequently the best two-point upper bound $\inf_{p\in(0,1)}U(p)$ on the robust objective equals $\lim_{p\to1^-}U(p)$; this is the first step of the proof of Proposition 7(a).
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 7, first paragraph

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue

namespace RobustMeanCov.OnePoint

theorem twoPointValue_antitoneOn (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m s : ℝ) (hs : 0 < s) :
    AntitoneOn (twoPointValue u m s) (Set.Ioo 0 1) := by sorry

end RobustMeanCov.OnePoint
