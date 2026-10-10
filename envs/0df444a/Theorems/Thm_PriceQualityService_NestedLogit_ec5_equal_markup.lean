-- Prove2me | Theorems.Thm_PriceQualityService_NestedLogit_ec5_equal_markup
-- name    : PriceQualityService.NestedLogit.ec5_equal_markup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:00.154982+00:00
-- url     : https://prove2.me/theorems/a8a44e33-41fc-449a-a042-0a53dbf90f74
-- title:
--   (EC.5), Online Supplement p. 5 — at an optimal price vector all products of a nest carry the same markup $1+r/\mu_1+(1-1/\mu_1)r_x$
-- statement:
--   Consider the two-stage nested logit model with nest coefficient $1/\mu_1$, $\mu_1\ge 1$, and production-cost coefficients $c_{xi}>0$. Fix a quality vector $\mathbf q$ and suppose that the price vector $\mathbf p$ maximizes the total expected profit $\Pi_M(\cdot,\mathbf q)$ over all price vectors. Let $r=\Pi_M(\mathbf p,\mathbf q)$ and let $r_x=\sum_{j=1}^{m_x}[p_{xj}-c_{xj}q_{xj}^2-t_x(a_{xj}-b_{xj}q_{xj})]\,d_{j|x}$ be the average profit of nest $x$. Then for every nest $x$ and every product $i$ of nest $x$,
--   $$
--   p_{xi}-c_{xi}q_{xi}^2-t_x(a_{xi}-b_{xi}q_{xi})=1+\frac{r}{\mu_1}+\Bigl(1-\frac1{\mu_1}\Bigr)r_x ,
--   $$
--   and consequently all products of the same nest have the same markup $\rho_x$.
--
--   This is the first dimension reduction of the proof of Theorem 4: the multi-product pricing problem becomes a problem in the two nest markups $\rho_s,\rho_l$.
--
--   **Formalization Note.** The paper derives the identity from the first-order condition $\partial\Pi_M/\partial p_{xi}=0$ at an optimum of the joint problem. Here it is stated for any price vector that is globally optimal for the given $\mathbf q$, which includes the price part of every joint optimum.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 5 (PDF p. 38), proof of Theorem 4, (EC.5)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Model

namespace PriceQualityService.NestedLogit

/-- (EC.5), Online Supplement p. 5 (proof of Theorem 4): if, for the quality vector `q`, the price
vector `p` maximizes the nested logit profit `Π_M(·, q)` over all price vectors, then every
product `i` of every nest `x` has markup
`p_xi − c_xi q_xi² − t_x (a_xi − b_xi q_xi) = 1 + r/μ₁ + (1 − 1/μ₁) r_x`, where `r = Π_M(p, q)` and
`r_x` is the average profit of nest `x`; in particular all products of a nest carry the same
markup. The paper obtains this from the first-order condition in `p_xi` at an optimum; here it is
stated as a property of a maximizer. -/
theorem ec5_equal_markup (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i)
    (p q : Vec M) (hmax : ∀ p' : Vec M, profit M p' q ≤ profit M p q) :
    (∀ (x : Nest) (i : Fin (M.m x)),
        markup M p q x i = 1 + profit M p q / M.μ₁ + (1 - 1 / M.μ₁) * nestAvgMarkup M p q x) ∧
      (∀ (x : Nest) (i j : Fin (M.m x)), markup M p q x i = markup M p q x j) := by sorry

end PriceQualityService.NestedLogit
