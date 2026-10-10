-- Prove2me | Theorems.Thm_PriceQualityService_NestedLogit_ec7_optimal_quality
-- name    : PriceQualityService.NestedLogit.ec7_optimal_quality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:29:03.33154+00:00
-- url     : https://prove2.me/theorems/9cf14b85-d42d-4296-80a0-615b3b3da391
-- title:
--   (EC.7), Online Supplement p. 6 — for every $r$ the qualities $q^\dagger_{xi}=(\alpha_{xi}+t_xb_{xi})/(2c_{xi})$ uniquely maximize the right-hand side
-- statement:
--   Consider the two-stage nested logit model with $\mu_1\ge 1$ and $c_{xi}>0$, and let $r$ be any real number. For a quality vector $\mathbf q$ put
--   $$
--   F(\mathbf q,r)=\sum_{x\in\{s,l\}}\mu_1\Bigl(\sum_{j=1}^{m_x}\exp\bigl(\alpha_{xj}q_{xj}-c_{xj}q_{xj}^2-t_x(a_{xj}-b_{xj}q_{xj})+t_xs_{xj}-r-\mu_1\bigr)\Bigr)^{1/\mu_1}.
--   $$
--   Then for every quality vector $\mathbf q$,
--   $$
--   F(\mathbf q,r)\le F(\mathbf q^\dagger,r),\qquad q^\dagger_{xi}=\frac{\alpha_{xi}+t_xb_{xi}}{2c_{xi}},
--   $$
--   and equality holds only for $\mathbf q=\mathbf q^\dagger$.
--
--   This is the quality step of the proof of Theorem 4: after the markups have been fixed at $r+\mu_1$, the optimal quality of each product depends only on its own parameters and on its nest's duration, not on the other products.
--
--   **Formalization Note.** The paper computes $\partial F/\partial q_{xi}$ "for any $r>0$"; the maximization statement holds for every real $r$ and is stated that way. The maximum is global over $\mathbb R^{m_s+m_l}$, not a first-order condition.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 6 (PDF p. 39), proof of Theorem 4, (EC.7)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Optimum

namespace PriceQualityService.NestedLogit

/-- (EC.7) and the optimal quality, Online Supplement p. 6 (proof of Theorem 4): for every real
`r`, the map
`q ↦ ∑_{x∈{s,l}} μ₁ (∑_j exp(α_xj q_xj − c_xj q_xj² − t_x (a_xj − b_xj q_xj) + t_x s_xj − r − μ₁))^{1/μ₁}`
attains its maximum over all quality vectors exactly at `q†`, `q†_xi = (α_xi + t_x b_xi)/(2c_xi)`. -/
theorem ec7_optimal_quality (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i)
    (r : ℝ) (q : Vec M) :
    fixedPointRHS M q r ≤ fixedPointRHS M (qDagger M) r ∧
      (fixedPointRHS M q r = fixedPointRHS M (qDagger M) r → q = qDagger M) := by sorry

end PriceQualityService.NestedLogit
