-- Prove2me | Theorems.Thm_PriceQualityService_uniform_duration_boundary
-- name    : PriceQualityService.uniform_duration_boundary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:42:42.300551+00:00
-- url     : https://prove2.me/theorems/e44256cb-6804-4871-bed2-eae87afd77f1
-- title:
--   Theorem 3 — the optimal uniform service duration is at a boundary point (corrected: boundary unless every duration is optimal)
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   In problem (7) every product carries the same service duration $t\in[t_s,t_l]$, prices are arbitrary reals and qualities range over a feasible set $Q$; the firm maximizes the MNL profit
--
--   $$
--   \Pi(\mathbf p,\mathbf q,t)=\sum_{i\in\mathcal N}\bigl[p_i-c_iq_i^2-t(a_i-b_iq_i)\bigr]\frac{\exp(\alpha_iq_i-p_i+ts_i)}{1+\sum_{j\in\mathcal N}\exp(\alpha_jq_j-p_j+ts_j)} .
--   $$
--
--   Let $(\mathbf p^*,\mathbf q^*,t^*)$ be an optimal solution of (7). Then
--
--   $$
--   t^*=t_s\quad\text{or}\quad t^*=t_l\quad\text{or}\quad\text{for every }t\in[t_s,t_l]\text{ there is }\mathbf p\text{ such that }(\mathbf p,\mathbf q^*,t)\text{ is optimal for (7)}.
--   $$
--
--   Under a uniform service policy, the firm should therefore offer either the shortest or the longest service duration to all products; an interior duration is optimal only in the degenerate case in which the duration does not affect the optimal profit at all, and then every duration (with the same qualities) is optimal.
--
--   **Formalization Note** Optimality means "at least the profit of every feasible point" (no supremum). The paper's quality domain is the instance $Q=\{\mathbf q:\ q_i\ge 0,\ q_i<a_i/b_i\text{ if }b_i>0\}$.
--
--   Differences from the source:
--   - correction: every optimal uniform duration t* satisfies t* = t_s or t* = t_l → t* = t_s ∨ t* = t_l ∨ every t ∈ [t_s, t_l] is optimal with the same quality vector q*; reason: counterexample satisfying every assumption: N = 1, α = s = a = c = 1, b = 0 (scenario (3)), [t_s, t_l] = [1, 2]; Π(p + t, q, t) = Π(p, q, 0), so the optimum ≈ 0.3371695 (q = 1/2) is attained at every t, e.g. t* = 3/2; the proof's "∂²y/∂t² > 0" (p. 30) fails when y is constant in t
--   - generalization: qualities in the domain of pp. 8–9 (q_i ≥ 0; q_i < a_i/b_i if b_i > 0) → an arbitrary quality set Q; reason: the argument keeps q* fixed and moves only p and t; Q = qualityDomain a b gives the paper's statement under either reading of scenario b_i = 0
--   - generalization: α_i > 0, s_i > 0, c_i > 0, 0 < t_s ≤ t_l (pp. 7–8) → arbitrary real α, s, a, b, c, t_s, t_l; reason: the proof uses none of them; where they fail the argument is unchanged or (7) has no optimal solution and the statement is vacuous
--   - encoding: optimal solution of max_{p,q,t} Π(p, q, t; N) with t_i = t → IsOptimalUniform: profit at (p, q, fun _ => t) ≥ profit at every feasible (p', q', fun _ => t'); reason: the definition of an optimal solution, without a supremum
--   - encoding: products 𝒩 = {1, …, N} → Fin N (N = 0 allowed); reason: Lean convention; N = 0 gives empty sums and changes no instance with N ≥ 1
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), p. 15, Theorem 3 (problem (7), p. 15); proof in App. B, pp. 29–30

import Mathlib
import Definitions.Def_PriceQualityService_IsOptimalUniform

namespace PriceQualityService

/-- **Theorem 3 (corrected): the optimal uniform service duration is at a boundary point unless
every duration is optimal.**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), Theorem 3, p. 15: "The optimal uniform service duration for all products in 𝒩 is always at
one of the boundary points, i.e., either `t* = t_s` or `t* = t_l`."

Let `(p, q, t)` be an optimal solution of problem (7) (prices in `ℝ^N`, qualities in `Q`, a
common duration `t ∈ [ts, tl]`). Then `t = ts`, or `t = tl`, or every duration
`t' ∈ [ts, tl]` is optimal too, together with the same quality vector `q` and a suitable price
vector `p'`.

**Formalization Note.** *Correction.* Read literally (every optimal `t*` is `t_s` or `t_l`), the
theorem is false: for `N = 1`, `α = s = a = c = 1`, `b = 0`, `[t_s, t_l] = [1, 2]`, the profit
satisfies `Π(p + t, q, t) = Π(p, q, 0)`, so the optimum (`≈ 0.3371695`, at `q = 1/2`) is attained
at every `t ∈ [1, 2]`, including `t = 3/2`. The third disjunct is the minimal correction; it
implies that some optimal solution has `t ∈ {t_s, t_l}`.
*Generalization.* The quality set `Q` is arbitrary (the paper's is `qualityDomain a b`), and
`α_i, s_i, c_i > 0`, `0 < t_s ≤ t_l` are not assumed. `N = 0` is allowed (then every point is
optimal). -/
theorem uniform_duration_boundary {N : ℕ} (α s a b c : Fin N → ℝ) (Q : Set (Fin N → ℝ))
    (ts tl : ℝ) (p q : Fin N → ℝ) (t : ℝ)
    (hopt : IsOptimalUniform α s a b c Q ts tl p q t) :
    t = ts ∨ t = tl ∨
      ∀ t' ∈ Set.Icc ts tl, ∃ p' : Fin N → ℝ, IsOptimalUniform α s a b c Q ts tl p' q t' := by sorry

end PriceQualityService
