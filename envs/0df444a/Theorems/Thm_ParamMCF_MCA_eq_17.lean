-- Prove2me | Theorems.Thm_ParamMCF_MCA_eq_17
-- name    : ParamMCF.MCA.eq_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:12.464819+00:00
-- url     : https://prove2.me/theorems/f67af832-4c81-4669-bd97-3c33d06225d4
-- title:
--   Equation (17), proof of Lemma 4, p. 16 — (15) on [−x^max, x^max] gives the two-sided edge-cost bound (17)
-- statement:
--   Fix one edge. Let $f$ be a marginal cost (strictly increasing, differentiable, $f(s)\le0$ for $s<0$ and $f(s)\ge0$ for $s>0$) and $\widetilde f$ a continuous function, with edge costs $F(x)=\int_0^x f(s)\,ds$ and $\widetilde F(x)=\int_0^x\widetilde f(s)\,ds$. Let $\alpha>1$, $\beta\ge0$, $m>0$ and $x^{\max}>0$. If
--
--   $$|\widetilde f(s)-f(s)|\le\frac{\alpha-1}{1+\alpha}|f(s)|+\frac{\beta}{(1+\alpha)m x^{\max}}\qquad(-x^{\max}\le s\le x^{\max}),\tag{15}$$
--
--   then for every $-x^{\max}\le x\le x^{\max}$
--
--   $$\frac{2}{1+\alpha}F(x)-\frac{\beta}{(1+\alpha)m}\le\widetilde F(x)\le\frac{2\alpha}{1+\alpha}F(x)+\frac{\beta}{(1+\alpha)m}.\tag{17}$$
--
--   This is the first case of the proof of Lemma 4: it turns the pointwise closeness (15) of marginal costs into a closeness of edge costs on the range where optimal flows live.
--
--   **Formalization Note** In Lemma 4, $m$ is the number of edges and $x^{\max}$ the maximal total inflow; here both are positive real parameters. Edge costs are integrated from $0$ (the paper's $\int_{l_e}^x$ agrees for the directed case $l_e=0$).
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 16, proof of Lemma 4, (15), (17)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- (17), proof of Lemma 4, p. 16: if the marginal costs satisfy (15) on `[-X, X]`, the edge costs
satisfy the two-sided bound (17) on `[-X, X]` (single edge; `X` is `xmax`, `m` the number of edges). -/
theorem eq_17 (g gt : ℝ → ℝ) (hg : IsMarginalCost g) (hgt : Continuous gt)
    (alpha beta m X : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta) (hm : 0 < m) (hX : 0 < X)
    (h15 : ∀ s ∈ Set.Icc (-X) X,
      |gt s - g s| ≤ (alpha - 1) / (1 + alpha) * |g s| + beta / ((1 + alpha) * m * X)) :
    ∀ x ∈ Set.Icc (-X) X,
      2 / (1 + alpha) * edgeCost g x - beta / ((1 + alpha) * m) ≤ edgeCost gt x ∧
        edgeCost gt x ≤ 2 * alpha / (1 + alpha) * edgeCost g x + beta / ((1 + alpha) * m) := by sorry

end ParamMCF.MCA
