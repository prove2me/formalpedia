-- Prove2me | Theorems.Thm_PriceQualityService_NestedLogit_ec6_markup_problem
-- name    : PriceQualityService.NestedLogit.ec6_markup_problem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:20.309473+00:00
-- url     : https://prove2.me/theorems/468b8209-d4a8-4443-bbb1-140553b03f1c
-- title:
--   (EC.6), Online Supplement pp. 5–6 — profit as a function of the nest markups, and $\rho_x-\mu_1=r$ at the optimal markups
-- statement:
--   Consider the two-stage nested logit model with $\mu_1\ge 1$ and $c_{xi}>0$, and fix a quality vector $\mathbf q$.
--
--   1. If every product of nest $x$ carries the same markup $\rho_x$, that is $p_{xi}-c_{xi}q_{xi}^2-t_x(a_{xi}-b_{xi}q_{xi})=\rho_x$ for all $x$ and $i$, then the profit (9) equals the markup profit (EC.6):
--   $$
--   \Pi_M(\mathbf p,\mathbf q)=\Pi_M(\boldsymbol\rho,\mathbf q)=\sum_{x\in\{s,l\}}\rho_x\cdot d_x(\boldsymbol\rho,\mathbf q).
--   $$
--   2. If the markup vector $\boldsymbol\rho=(\rho_s,\rho_l)$ maximizes $\Pi_M(\cdot,\mathbf q)$ over $\mathbb R^2$, then for every nonempty nest $x$,
--   $$
--   \rho_x-\mu_1=\Pi_M(\boldsymbol\rho,\mathbf q).
--   $$
--
--   This is the second dimension reduction of the proof of Theorem 4: at the optimum the nest-level markup is the same for both nests and equals the optimal profit plus $\mu_1$, the reciprocal of the nest coefficient.
--
--   **Formalization Note.** The paper obtains part 2 from the first-order condition $\partial\Pi_M(\boldsymbol\rho,\mathbf q)/\partial\rho_x=0$; here it is stated for a global maximizer. An empty nest is never chosen, so its markup is not determined by optimality; part 2 is therefore stated for nonempty nests only.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement pp. 5–6 (PDF pp. 38–39), proof of Theorem 4, (EC.6)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_MarkupProblem

namespace PriceQualityService.NestedLogit

/-- (EC.6), Online Supplement pp. 5–6 (proof of Theorem 4).
1. If every product of nest `x` carries the same markup `ρ_x`, the profit (9) equals the
   two-dimensional markup profit `Π_M(ρ, q) = ∑_x ρ_x d_x(ρ, q)`.
2. For a fixed quality vector `q`, if the nest markups `ρ = (ρ_s, ρ_l)` maximize `Π_M(·, q)`,
   then `ρ_x − μ₁ = Π_M(ρ, q)` for every nonempty nest `x`.
The paper obtains (2) from the first-order condition in `ρ_x`; here it is stated as a property of
a maximizer. An empty nest has `d_x = 0`, so its markup is not determined, whence `0 < m_x`. -/
theorem ec6_markup_problem (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) :
    (∀ (p : Vec M) (ρ : Nest → ℝ), (∀ (x : Nest) (i : Fin (M.m x)), markup M p q x i = ρ x) →
        profit M p q = markupProfit M ρ q) ∧
      (∀ ρ : Nest → ℝ, (∀ ρ' : Nest → ℝ, markupProfit M ρ' q ≤ markupProfit M ρ q) →
        ∀ x : Nest, 0 < M.m x → ρ x - M.μ₁ = markupProfit M ρ q) := by sorry

end PriceQualityService.NestedLogit
