-- Prove2me | Theorems.Thm_ParamMCF_MCA_case_16
-- name    : ParamMCF.MCA.case_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:05.982989+00:00
-- url     : https://prove2.me/theorems/f6512819-91ed-4d79-a9e1-cfc0bf39cf03
-- title:
--   Proof of Lemma 4, p. 17 — |f̃| ≥ |f| and (16) on [−x^max, x^max] give F ≤ F̃ ≤ αF + β/m
-- statement:
--   Fix one edge. Let $f$ be a marginal cost (strictly increasing, differentiable, $f(s)\le0$ for $s<0$ and $f(s)\ge0$ for $s>0$) and let $\widetilde f$ be continuous with the same sign pattern, $\widetilde f(s)\le0$ for $s<0$ and $\widetilde f(s)\ge0$ for $s>0$. Write $F(x)=\int_0^x f$ and $\widetilde F(x)=\int_0^x\widetilde f$. Let $\alpha>1$, $\beta\ge0$, $m>0$, $x^{\max}>0$, and suppose that for all $-x^{\max}\le s\le x^{\max}$ both $|\widetilde f(s)|\ge|f(s)|$ and
--
--   $$|\widetilde f(s)-f(s)|\le(\alpha-1)|f(s)|+\frac{\beta}{m x^{\max}}.\tag{16}$$
--
--   Then for every $-x^{\max}\le x\le x^{\max}$
--
--   $$F(x)\le\widetilde F(x)\le\alpha F(x)+\frac{\beta}{m}.$$
--
--   This is the second case of the proof of Lemma 4.
--
--   **Formalization Note** The sign condition on $\widetilde f$ is the standing assumption of §5.2 on marginal costs, and it is needed: without it, $\widetilde f=-2f$ satisfies $|\widetilde f|\ge|f|$ and, for $\alpha\ge4$, (16), yet $\widetilde F<0\le F$. Edge costs are integrated from $0$.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 17, proof of Lemma 4, second case, (16)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- The (16) case of the proof of Lemma 4, p. 17: if `|gt| ≥ |g|` and (16) hold on `[-X, X]`, then
`F ≤ F̃ ≤ αF + β/m` on `[-X, X]` (single edge; `gt` is sign preserving, the §5.2 standing assumption). -/
theorem case_16 (g gt : ℝ → ℝ) (hg : IsMarginalCost g)
    (hgt : Continuous gt ∧ (∀ s, 0 < s → 0 ≤ gt s) ∧ (∀ s, s < 0 → gt s ≤ 0))
    (alpha beta m X : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta) (hm : 0 < m) (hX : 0 < X)
    (hge : ∀ s ∈ Set.Icc (-X) X, |g s| ≤ |gt s|)
    (h16 : ∀ s ∈ Set.Icc (-X) X,
      |gt s - g s| ≤ (alpha - 1) * |g s| + beta / (m * X)) :
    ∀ x ∈ Set.Icc (-X) X,
      edgeCost g x ≤ edgeCost gt x ∧ edgeCost gt x ≤ alpha * edgeCost g x + beta / m := by sorry

end ParamMCF.MCA
