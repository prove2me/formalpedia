-- Prove2me | Theorems.Thm_PriceQualityService_NestedLogit_theorem_4
-- name    : PriceQualityService.NestedLogit.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:29:12.794422+00:00
-- url     : https://prove2.me/theorems/b6a00cae-e6c5-43de-afd0-dba814b90134
-- title:
--   Theorem 4, p. 19 — nested logit joint optimum: $q^\dagger_{xi}=(\alpha_{xi}+t_xb_{xi})/(2c_{xi})$, common markup $\mu_1+r^\dagger$, optimal profit $r^\dagger$
-- statement:
--   Consider a firm selling products in two nests $x\in\{s,l\}$ with fixed service durations $t_s,t_l$, under the two-stage nested logit model with upper-level scale $\mu_1\ge1$ (nest coefficient $1/\mu_1$) and production-cost coefficients $c_{xi}>0$. The firm chooses prices $\mathbf p$ and qualities $\mathbf q$ to maximize the total expected profit $\Pi_M(\mathbf p,\mathbf q)$ of (9). Define
--   $$
--   q^\dagger_{xi}=\frac{\alpha_{xi}+t_xb_{xi}}{2c_{xi}} .
--   $$
--   Then:
--   1. the equation in $r$
--   $$
--   r=\sum_{x\in\{s,l\}}\mu_1\Bigl(\sum_{i=1}^{m_x}\exp\bigl(\alpha_{xi}q^\dagger_{xi}-c_{xi}q^{\dagger2}_{xi}-t_x(a_{xi}-b_{xi}q^\dagger_{xi})+t_xs_{xi}-r-\mu_1\bigr)\Bigr)^{1/\mu_1}
--   $$
--   has a unique real solution $r^\dagger$;
--   2. with $p^\dagger_{xi}=\mu_1+r^\dagger+c_{xi}q^{\dagger2}_{xi}+t_x(a_{xi}-b_{xi}q^\dagger_{xi})$, the decisions $(\mathbf p^\dagger,\mathbf q^\dagger)$ maximize $\Pi_M$ over all real price and quality vectors;
--   3. the optimal profit is $\Pi_M(\mathbf p^\dagger,\mathbf q^\dagger)=r^\dagger$;
--   4. $(\mathbf p^\dagger,\mathbf q^\dagger)$ is the only maximizer.
--
--   The result says that, as under the multinomial logit model, each product's optimal quality depends only on its own parameters and its nest's duration, and that at the optimum every product, in either nest, carries the same markup $\mu_1+r^\dagger$.
--
--   **Formalization Note.** Optimality is global: (2) quantifies over all $(\mathbf p,\mathbf q)\in\mathbb R^{m_s+m_l}\times\mathbb R^{m_s+m_l}$; the paper's proof uses first-order conditions. Clause (4) is the reading of "the optimal quality level ... is given by" and "the optimal price ... can be expressed as" as statements about every optimum. Empty nests are allowed; an empty nest contributes nothing to the sum.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 19, Theorem 4; proof in Online Supplement pp. 5–6 (PDF pp. 38–39)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Optimum

namespace PriceQualityService.NestedLogit

/-- Theorem 4, p. 19 (Wang, Ke & Cui), joint price and quality optimization under the two-stage
nested logit model with fixed nests and nest durations, `μ₁ ≥ 1` and `c_xi > 0`. There is a real
number `r†` such that
1. `r†` solves `r = ∑_{x∈{s,l}} μ₁ (∑_i exp(α_xi q†_xi − c_xi q†_xi² − t_x (a_xi − b_xi q†_xi) + t_x s_xi − r − μ₁))^{1/μ₁}`,
   and it is the only real solution;
2. with `q†_xi = (α_xi + t_x b_xi)/(2c_xi)` and `p†_xi = μ₁ + r† + c_xi q†_xi² + t_x (a_xi − b_xi q†_xi)`,
   `(p†, q†)` maximizes the profit `Π_M` of (9) over all price and quality vectors;
3. the optimal profit `Π_M(p†, q†)` equals `r†`;
4. every maximizer `(p, q)` of `Π_M` is `(p†, q†)`. -/
theorem theorem_4 (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i) :
    ∃ rDag : ℝ,
      rDag = fixedPointRHS M (qDagger M) rDag ∧
      (∀ r : ℝ, r = fixedPointRHS M (qDagger M) r → r = rDag) ∧
      (∀ p q : Vec M, profit M p q ≤ profit M (pDagger M rDag) (qDagger M)) ∧
      profit M (pDagger M rDag) (qDagger M) = rDag ∧
      (∀ p q : Vec M, (∀ p' q' : Vec M, profit M p' q' ≤ profit M p q) →
        q = qDagger M ∧ p = pDagger M rDag) := by sorry

end PriceQualityService.NestedLogit
