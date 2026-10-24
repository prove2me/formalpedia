-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_cubic_ineq_iff_pmu_nonneg
-- name    : ProjSelfConcordant.ConicExt.cubic_ineq_iff_pmu_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:04.36172+00:00
-- url     : https://prove2.me/theorems/ec6500d5-59ca-46a1-9c5c-001953a19dd8
-- title:
--   §2, p. 5 — the cubic inequality in α is equivalent to p_μ(t) ≥ 0 for all t
-- statement:
--   Let $a,b,c,\nu$ be real numbers with $c_2=b-a^2>0$ (in the paper $a=f'(\tilde x)[\tilde v]$, $b=f''(\tilde x)[\tilde v,\tilde v]$, $c=f'''(\tilde x)[\tilde v,\tilde v,\tilde v]$). Put $c_3=c-6ba+4a^3$ and $\mu=c_2^{-3/2}c_3$. Then
--   $$\bigl(-2\alpha^3+6\alpha^2a-6\alpha b+c\bigr)^2\le4\nu\bigl(\alpha^2-2\alpha a+b\bigr)^3\ \ \forall\alpha\in\mathbb R$$
--   holds if and only if
--   $$p_\mu(t)=4(\nu-1)t^6+12(\nu-2)t^4+4\mu t^3+12(\nu-3)t^2+12\mu t+4\nu-\mu^2\ge0\ \ \forall t\in\mathbb R.$$
--
--   The substitution $t=c_2^{-1/2}(\alpha-a)$ normalizes the affine self-concordance inequality along a two-dimensional slice into a one-parameter family of sextics, reducing Theorem 1.5 to a question about the single number $\mu$.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 (the 'or equivalently' display defining p_µ)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: with `a = f′(x̃)[ṽ]`, `b = f″(x̃)[ṽ,ṽ]`, `c = f‴(x̃)[ṽ,ṽ,ṽ]`, `c₂ = b − a² > 0`,
`c₃ = c − 6ab + 4a³` and `μ = c₂^{−3/2}c₃`, the inequality
`(−2α³ + 6α²a − 6αb + c)² ≤ 4ν(α² − 2αa + b)³` for all real `α` is equivalent to
`p_μ(t) ≥ 0` for all real `t`. -/
theorem cubic_ineq_iff_pmu_nonneg (a b c ν : ℝ) (hc2 : 0 < b - a ^ 2) :
    (∀ α : ℝ, (-2 * α ^ 3 + 6 * α ^ 2 * a - 6 * α * b + c) ^ 2
        ≤ 4 * ν * (α ^ 2 - 2 * α * a + b) ^ 3) ↔
      ∀ t : ℝ, 0 ≤ pmu ν ((c - 6 * b * a + 4 * a ^ 3) / (b - a ^ 2) ^ (3 / 2 : ℝ)) t := by sorry

end ProjSelfConcordant.ConicExt
