-- Prove2me | Theorems.Thm_PriceQualityService_yValue_convex
-- name    : PriceQualityService.yValue_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:42:00.825995+00:00
-- url     : https://prove2.me/theorems/94c766b4-c373-434a-b4e1-2d481eb8f33d
-- title:
--   Proof of Theorem 3, p. 30 — $y$ is convex in the uniform service duration
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   Fix a quality vector $\mathbf q$. The function
--
--   $$
--   t\longmapsto y(\mathbf q,t)=\sum_{i\in\mathcal N}\exp\Bigl(\alpha_iq_i-c_iq_i^2+t\bigl(s_i-(a_i-b_iq_i)\bigr)\Bigr)
--   $$
--
--   is convex on $\mathbb R$.
--
--   Convexity of $y$ in the common duration is what places the optimal uniform duration at an end of $[t_s,t_l]$.
--
--   **Formalization Note** The claim is convexity, not strict convexity: the paper's computation "$\partial^2y/\partial t^2>0$" fails when $y$ does not depend on $t$ (e.g. all $b_i=0$ and $s_i=a_i$).
--
--   Differences from the source:
--   - reading: y evaluated at the unconstrained optimal quality q_i = (α_i + t b_i)/(2c_i) → y at a fixed quality vector q; reason: the form the argument needs under a quality constraint; it is the paper's y when q is that point
--   - generalization: convex in the service duration t (durations in [t_s, t_l]); α_i, s_i, c_i > 0 → convex on all of ℝ; arbitrary real parameters; reason: each exponent is affine in t for fixed q; restricting to [t_s, t_l] gives the paper's claim
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), p. 30 (unnumbered)

import Mathlib
import Definitions.Def_PriceQualityService_yValue

namespace PriceQualityService

/-- **`y` is convex in the uniform service duration.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), unnumbered, p. 30: "Let
`y = Σ_{i∈𝒩} exp(b_i²t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i))t + α_i²/(4c_i))`. … Thus, y is a convex
function in service duration t."

For every fixed quality vector `q`, the map `t ↦ y(q, t) = Σ_i exp(α_i q_i − c_i q_i² + t(s_i − (a_i − b_i q_i)))`
is convex on all of `ℝ`.

**Formalization Note.** Convexity, not strict convexity: the paper's "`∂²y/∂t² > 0`" fails when
`y` is constant in `t` (e.g. all `b_i = 0` and `s_i = a_i`). `y` is taken at a fixed quality
vector rather than at the unconstrained optimal quality `(α_i + t b_i)/(2c_i)`. -/
theorem yValue_convex {N : ℕ} (α s a b c q : Fin N → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => yValue α s a b c q (fun _ => t)) := by sorry

end PriceQualityService
