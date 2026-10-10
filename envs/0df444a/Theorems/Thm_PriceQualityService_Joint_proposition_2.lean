-- Prove2me | Theorems.Thm_PriceQualityService_Joint_proposition_2
-- name    : PriceQualityService.Joint.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:05.692966+00:00
-- url     : https://prove2.me/theorems/40df0d66-d8e5-43c8-b27c-8b8da6c7685a
-- title:
--   Proposition 2: which extreme service duration is optimal for each product
-- statement:
--   Assume $c_i>0$ for every product and $t_s\le t_l$. For each product $i$ define the duration $t_i^*$ by:
--
--   1. if $b_i\ne0$: $t_i^*=t_s$ when $\bigl(2(a_i-s_i)c_i-\alpha_ib_i\bigr)/b_i^2\ge(t_s+t_l)/2$, and $t_i^*=t_l$ otherwise;
--   2. if $b_i=0$: $t_i^*=t_s$ when $a_i>s_i$, and $t_i^*=t_l$ otherwise.
--
--   Then $\mathbf t^*$ is an optimal duration vector for the joint problem (4): there are prices $\mathbf p$ and qualities $\mathbf q$ such that
--   $$
--   \Pi(\mathbf p',\mathbf q',\mathbf t';\mathcal N)\le\Pi(\mathbf p,\mathbf q,\mathbf t^*;\mathcal N)
--   $$
--   for all prices $\mathbf p'$, all qualities $\mathbf q'$ and all durations $\mathbf t'\in[t_s,t_l]^N$. Moreover, when $t_s<t_l$, every optimal solution $(\mathbf p,\mathbf q,\mathbf t)$ of (4) has $t_i=t_i^*$ for every product $i$ whose case is strict: $b_i\ne0$ and $\bigl(2(a_i-s_i)c_i-\alpha_ib_i\bigr)/b_i^2\ne(t_s+t_l)/2$, or $b_i=0$ and $a_i\ne s_i$.
--
--   The proposition tells the firm which products receive the shortest and which the longest service, using only each product's own parameters.
--
--   **Formalization Note** At the threshold $\bigl(2(a_i-s_i)c_i-\alpha_ib_i\bigr)/b_i^2=(t_s+t_l)/2$ both endpoints are optimal; the statement says that the paper's choice is *an* optimal duration, and that it is the only optimal duration of product $i$ outside the tie cases (threshold equality when $b_i\ne0$; $a_i=s_i$ when $b_i=0$) and when $t_s<t_l$. $c_i>0$ is the paper's convex production cost (p. 8). Qualities range over $\mathbb R$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 11, Proposition 2; proof p. 27, Appendix B, Proof of Theorem 1

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- Proposition 2, p. 11: choose for each product `i` the duration
`t*_i = t_s` if `b_i ≠ 0` and `(2(a_i − s_i)c_i − α_i b_i)/b_i² ≥ (t_s + t_l)/2`, or if `b_i = 0` and
`a_i > s_i`; and `t*_i = t_l` otherwise. Then `t*` is an optimal duration vector of problem (4): for
some prices `p` and qualities `q`, `(p, q, t*)` maximizes the profit (3) over all prices, all
qualities and all durations in `[t_s, t_l]^N`. Moreover, when `t_s < t_l`, every optimal solution
`(p, q, t)` of (4) has `t_i = t*_i` for every product `i` whose case is strict (`b_i ≠ 0` and
`(2(a_i − s_i)c_i − α_i b_i)/b_i² ≠ (t_s + t_l)/2`, or `b_i = 0` and `a_i ≠ s_i`); in the tie cases both
endpoints are optimal, so the page's "the optimal service duration" is read as "an optimal
duration", and as "the only optimal duration" outside the ties. -/
theorem proposition_2 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) :
    let tstar : Fin N → ℝ := fun i =>
      if b i ≠ 0 then
        (if (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2 then ts else tl)
      else (if a i > s i then ts else tl)
    (∃ p q : Fin N → ℝ, ∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
      profit α a b c s p' q' t' ≤ profit α a b c s p q tstar) ∧
    (ts < tl → ∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
      (∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
          profit α a b c s p' q' t' ≤ profit α a b c s p q t) →
      ∀ i, ((b i ≠ 0 ∧ (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≠ (ts + tl) / 2) ∨
          (b i = 0 ∧ a i ≠ s i)) →
        t i = tstar i) := by sorry

end PriceQualityService.Joint
