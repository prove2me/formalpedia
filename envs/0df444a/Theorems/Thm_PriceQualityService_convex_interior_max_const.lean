-- Prove2me | Theorems.Thm_PriceQualityService_convex_interior_max_const
-- name    : PriceQualityService.convex_interior_max_const
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:42:14.642259+00:00
-- url     : https://prove2.me/theorems/7666ee3f-fd2b-4de2-877a-5dd47fecde62
-- title:
--   Proof of Theorem 3, p. 30 — endpoint step (corrected: an interior maximizer of a convex function forces it to be constant)
-- statement:
--   Let $t_s,t_l\in\mathbb R$ and let $f:\mathbb R\to\mathbb R$ be convex on $[t_s,t_l]$. If $f$ attains its maximum over $[t_s,t_l]$ at an interior point $t\in(t_s,t_l)$, that is $f(t')\le f(t)$ for all $t'\in[t_s,t_l]$, then
--
--   $$
--   f(t')=f(t)\qquad\text{for all }t'\in[t_s,t_l].
--   $$
--
--   Applied to $f=y(\mathbf q^*,\cdot)$, this is the step from "$y$ is convex in $t$" to "the optimal uniform duration is at a boundary point": an optimal duration is $t_s$ or $t_l$ unless $y$, and hence the optimal profit, does not depend on the duration at all. The complementary fact that a convex function on $[t_s,t_l]$ is bounded by $\max(f(t_s),f(t_l))$ is in Mathlib.
--
--   Differences from the source:
--   - correction: y convex in t, hence "the optimal uniform service duration t* is at one of the boundary points" → a convex f maximized at an interior t is constant on [t_s, t_l]; reason: a convex function can be maximized at interior points (f constant); in the paper's model this happens for N = 1, α = s = a = c = 1, b = 0, [t_s, t_l] = [1, 2], where every t is optimal (see the main theorem)
--   - generalization: f = y, the aggregate attraction → any function convex on [t_s, t_l]; reason: the step uses only convexity; f = y(q*, ·) is the instance
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), p. 30 (unnumbered, last paragraph)

import Mathlib

namespace PriceQualityService

/-- **The endpoint step: a convex function maximized at an interior point is constant.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), unnumbered, p. 30: "Thus, y is a convex function in service
duration t. Then the optimal uniform service duration `t*` is at one of the boundary points,
i.e., `t* = t_s` or `t* = t_l`."

If `f` is convex on `[ts, tl]` and attains its maximum over `[ts, tl]` at an interior point
`t ∈ (ts, tl)`, then `f` is constant on `[ts, tl]`.

**Formalization Note.** This is the corrected content of the quoted step: a convex function's
maximizers need not be endpoints (a constant function is maximized everywhere), but an interior
maximizer forces `f` to be constant. The other half, that a convex function on `[ts, tl]` is
bounded by `max (f ts) (f tl)`, is Mathlib's `ConvexOn.le_on_segment`. -/
theorem convex_interior_max_const {f : ℝ → ℝ} {ts tl t : ℝ}
    (hf : ConvexOn ℝ (Set.Icc ts tl) f) (ht : t ∈ Set.Ioo ts tl)
    (hmax : ∀ t' ∈ Set.Icc ts tl, f t' ≤ f t) :
    ∀ t' ∈ Set.Icc ts tl, f t' = f t := by sorry

end PriceQualityService
