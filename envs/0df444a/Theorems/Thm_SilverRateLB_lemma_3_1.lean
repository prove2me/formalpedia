-- Prove2me | Theorems.Thm_SilverRateLB_lemma_3_1
-- name    : SilverRateLB.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:33.263743+00:00
-- url     : https://prove2.me/theorems/26db65f5-f715-464c-be51-6082da1f6b22
-- title:
--   Lemma 3.1 — gap trajectory with arc vectors and projections onto K
-- statement:
--   Let $\varepsilon,\gamma>0$, $c=\sqrt{1+2\gamma+\varepsilon^2}$, $R=\sqrt{\varepsilon^2+(1+\gamma)^2}$, and let $K\subset\mathbb R^2$ be the convex hull of the origin and the arc $\{v(q):0\le q\le1\}$, $v(q)=(\sqrt{R^2-(q+\gamma)^2},-q)$. For every $m\ge0$ and nonnegative $\alpha_1,\dots,\alpha_m$ there are points $r_0,\dots,r_m$ and arc vectors $v_j=v(q_j)$, $q_j\in[0,1]$, $0\le j\le m$, such that
--   $$r_m=v_m=(\varepsilon,-1),\qquad r_j=r_{j-1}-\alpha_jv_{j-1}\ (1\le j\le m),\qquad v_j=\Pi_K(r_j)\ (0\le j\le m),$$
--   and, with $S=\sum_{j=1}^m\alpha_j$,
--   $$r_0=(\varepsilon+P,-1-Q),\qquad 0\le P\le cS,\qquad 0\le Q\le\Bigl[\frac{c(1+\gamma+R)}{\varepsilon(\gamma+R)}\Bigr]^{R/\gamma}-1.$$
--   Each update has the form of a gradient step with stepsize $\alpha_j$ and gradient $v_{j-1}$; after scaling, the trajectory becomes the gradient-descent trajectory of a local hard function during one gap (Lemma 3.2).
--
--   **Formalization Note** $\Pi_K(r)=v$ is the published predicate `OrabonaOL.OGD.IsEuclideanProj`: $v\in K$ minimizes the distance to $r$ over $K$.
--
--   Differences from the source:
--   - encoding: finite families r_0, …, r_m, v_0, …, v_m, α_1, …, α_m → sequences ℕ → ·, used on the printed index ranges; reason: same data
--   - encoding: v_j = Π_K(r_j) → IsEuclideanProj K r_j v_j; reason: for nonempty closed convex K the projection exists and is unique, so the predicate is the map
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 3.1, p. 11

import Mathlib
import Definitions.Def_SilverRateLB_arcSet
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj

namespace SilverRateLB

/-- **Lemma 3.1 (gap trajectory).** Let `ε, γ > 0`, `c = √(1+2γ+ε²)`, `R = √(ε²+(1+γ)²)` and
`K = conv({0} ∪ {v(q) : 0 ≤ q ≤ 1})`. For every `m ≥ 0` and nonnegative `α_1, …, α_m` there are
points `r_0, …, r_m` and arc vectors `v_0, …, v_m` with `r_m = v_m = (ε, −1)`,
`r_j = r_{j−1} − α_j v_{j−1}` (`1 ≤ j ≤ m`), `v_j = Π_K(r_j)` (`0 ≤ j ≤ m`), and, with
`S = ∑ α_j`, `r_0 = (ε + P, −1 − Q)`, `0 ≤ P ≤ cS`,
`0 ≤ Q ≤ [c(1+γ+R)/(ε(γ+R))]^{R/γ} − 1`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 3.1, p. 11 (proof §A.1, pp. 20–23).

**Formalization Note** The sequences are indexed by `ℕ` and used on `0 ≤ j ≤ m`; `α` is used on
`1 ≤ j ≤ m`. "Arc vector" is `v_j = arcVec ε γ q_j` with `q_j ∈ [0, 1]`. `Π_K(r) = v` is
`OrabonaOL.OGD.IsEuclideanProj K r v` (`v ∈ K` minimizes the distance to `r`). -/
theorem lemma_3_1 (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (m : ℕ) (α : ℕ → ℝ)
    (hα : ∀ j ∈ Finset.Icc 1 m, 0 ≤ α j) :
    ∃ (r v : ℕ → EuclideanSpace ℝ (Fin 2)) (q : ℕ → ℝ),
      (∀ j ≤ m, q j ∈ Set.Icc (0 : ℝ) 1 ∧ v j = arcVec ε γ (q j)) ∧
      r m = !₂[ε, -1] ∧ v m = !₂[ε, -1] ∧
      (∀ j ∈ Finset.Icc 1 m, r j = r (j - 1) - α j • v (j - 1)) ∧
      (∀ j ≤ m, OrabonaOL.OGD.IsEuclideanProj (arcSet ε γ) (r j) (v j)) ∧
      ∃ P Q : ℝ, r 0 = !₂[ε + P, -1 - Q] ∧
        0 ≤ P ∧ P ≤ cOf ε γ * ∑ j ∈ Finset.Icc 1 m, α j ∧
        0 ≤ Q ∧ Q ≤ ((cOf ε γ * (1 + γ + ROf ε γ)) / (ε * (γ + ROf ε γ))) ^ (ROf ε γ / γ) - 1 := by sorry

end SilverRateLB
