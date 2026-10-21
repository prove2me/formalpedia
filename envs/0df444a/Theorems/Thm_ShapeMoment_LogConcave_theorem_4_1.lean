-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_theorem_4_1
-- name    : ShapeMoment.LogConcave.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:42.213324+00:00
-- url     : https://prove2.me/theorems/2872fe97-14f3-4a3a-a3c7-7a4523ff4489
-- title:
--   Theorem 4.1 — every optimal extreme point is piecewise geometric
-- statement:
--   Assume (DMP-LC) is feasible and $q_0=1$. An optimal extreme point exists. Every optimal extreme point $x^*$ has consecutive support $[k,\ell]$ and at most $m$ geometric pieces: for weakly increasing breakpoints $k=b_0\le\cdots\le b_m=\ell$ and positive $\alpha_i,r_i$,
--
--   $$x^*_j=\alpha_i r_i^{j-b_{i-1}}\quad(b_{i-1}\le j\le b_i),\qquad x^*_j=0\quad(j\notin[k,\ell]).$$
--
--   Coordinates on the support are positive. **Formalization Note** The printed $r_i<1$ and strict breakpoint chain both fail on valid instances, so the statement uses positive ratios and permits degenerate pieces. At $m=0$, it states the optimal extreme point is a point mass.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 13, Theorem 4.1, equation (15), corrected

import Definitions.Def_ShapeMoment_LogConcave_Model

namespace ShapeMoment.LogConcave

theorem theorem_4_1 (n m : ℕ) (f : Fin n → ℝ) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hfeas : (feasLC n m q).Nonempty) :
    (∃ x ∈ (feasLC n m q).extremePoints ℝ,
      IsMaxSol f (feasLC n m q) x) ∧
    ∀ x ∈ (feasLC n m q).extremePoints ℝ,
      IsMaxSol f (feasLC n m q) x →
      ∃ (k ℓ : ℕ) (breakpoint : Fin (m + 1) → ℕ)
        (α r : Fin m → ℝ),
        1 ≤ k ∧ k ≤ ℓ ∧ ℓ ≤ n ∧
        Monotone breakpoint ∧ breakpoint 0 = k ∧
        breakpoint (Fin.last m) = ℓ ∧
        (∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j) ∧
        (∀ j, (j < k ∨ ℓ < j) → ext x j = 0) ∧
        (∀ i, 0 < α i ∧ 0 < r i) ∧
        (∀ i : Fin m, ∀ j, breakpoint i.castSucc ≤ j →
          j ≤ breakpoint i.succ →
          ext x j = α i * r i ^ (j - breakpoint i.castSucc)) := by sorry

end ShapeMoment.LogConcave
