-- Prove2me | Theorems.Thm_PriceQualityService_optimal_uniform_iff_yValue
-- name    : PriceQualityService.optimal_uniform_iff_yValue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:41:39.594535+00:00
-- url     : https://prove2.me/theorems/c1e6c476-e0cd-4717-a79e-fd781497f363
-- title:
--   Proof of Theorem 3, p. 30 — problem (7) reduces to maximizing $y$
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   Let $Q\subseteq\mathbb R^N$ be the feasible quality set and $[t_s,t_l]$ the duration interval. For a quality vector $\mathbf q$ and a common duration $t$ write
--
--   $$
--   y(\mathbf q,t)=\sum_{i\in\mathcal N}\exp\Bigl(\alpha_iq_i-c_iq_i^2+t\bigl(s_i-(a_i-b_iq_i)\bigr)\Bigr).
--   $$
--
--   Then there is a price vector $\mathbf p$ such that $(\mathbf p,\mathbf q,t)$ is an optimal solution of problem (7) if and only if $\mathbf q\in Q$, $t\in[t_s,t_l]$, and
--
--   $$
--   y(\mathbf q',t')\le y(\mathbf q,t)\qquad\text{for all }\mathbf q'\in Q,\ t'\in[t_s,t_l].
--   $$
--
--   After prices are optimized, the profit is an increasing function of the aggregate attraction $y$, so the uniform-duration problem is the maximization of $y$ over qualities and the common duration.
--
--   Differences from the source:
--   - reading: y evaluated at the unconstrained optimal quality q_i = (α_i + t b_i)/(2c_i) → y at a free quality vector q, maximized over the feasible set Q; reason: the unconstrained optimum can leave the quality domain (e.g. b_i < 0, t > α_i/|b_i| gives q_i < 0); at that point the two agree
--   - generalization: the quality domain of pp. 8–9; α_i, s_i, c_i > 0; 0 < t_s ≤ t_l → an arbitrary quality set Q; arbitrary real parameters and t_s, t_l; reason: the reduction uses none of these; Q = qualityDomain a b gives the paper's problem
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), p. 30 (unnumbered, after eq. (25))

import Mathlib
import Definitions.Def_PriceQualityService_IsOptimalUniform
import Definitions.Def_PriceQualityService_yValue

namespace PriceQualityService

/-- **Problem (7) reduces to maximizing `y`.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), proof of Theorem 3 (App. B), unnumbered, p. 30: "We observe that the optimization problem in
terms of t is only related to the numerator of the RHS for any r > 0."

For a quality vector `q` and a uniform duration `t`: some price vector `p` makes `(p, q, t)` an
optimal solution of (7) if and only if `q ∈ Q`, `t ∈ [ts, tl]` and `(q, t)` maximizes
`y(q', t') = Σ_i exp(α_i q'_i − c_i q'_i² + t'(s_i − (a_i − b_i q'_i)))` over `Q × [ts, tl]`.

**Formalization Note.** The paper's `y` is evaluated at the unconstrained optimal quality
`q_i = (α_i + t b_i)/(2c_i)`; here `y` is taken at a free quality vector and the maximization
ranges over the feasible quality set `Q`, which may be any set (the paper's domain is
`qualityDomain a b`). No sign assumptions on the parameters, and `ts ≤ tl` is not assumed. -/
theorem optimal_uniform_iff_yValue {N : ℕ} (α s a b c : Fin N → ℝ) (Q : Set (Fin N → ℝ))
    (ts tl : ℝ) (q : Fin N → ℝ) (t : ℝ) :
    (∃ p : Fin N → ℝ, IsOptimalUniform α s a b c Q ts tl p q t) ↔
      (q ∈ Q ∧ t ∈ Set.Icc ts tl ∧
        ∀ q' ∈ Q, ∀ t' ∈ Set.Icc ts tl,
          yValue α s a b c q' (fun _ => t') ≤ yValue α s a b c q (fun _ => t)) := by sorry

end PriceQualityService
