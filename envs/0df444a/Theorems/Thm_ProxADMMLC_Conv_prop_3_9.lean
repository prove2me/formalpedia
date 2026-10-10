-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_prop_3_9
-- name    : ProxADMMLC.Conv.prop_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:17.421983+00:00
-- url     : https://prove2.me/theorems/47656fe0-65bd-409a-95e8-5991afa76612
-- title:
--   Proposition 3.9 (Hoffman bound), p. 2282 — dist(x̄, S)² ≤ θ²(‖(Ax̄ − b)₊‖² + ‖Cx̄ − d‖²), θ depending on A, C only
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ and $C\in\mathbb R^{k\times n}$. There is a constant $\theta>0$, depending on $A$ and $C$ only, such that for all $b\in\mathbb R^m$ and $d\in\mathbb R^k$ for which the polyhedron
--   $$S=\{x\in\mathbb R^n:\ Ax\le b,\ Cx=d\}$$
--   is nonempty, and for every point $\bar x\in\mathbb R^n$,
--   $$\operatorname{dist}(\bar x,S)^2\ \le\ \theta^2\big(\|(A\bar x-b)_+\|^2+\|C\bar x-d\|^2\big),$$
--   where $(v)_+$ is the projection onto the nonnegative orthant and $Ax\le b$ is meant componentwise.
--
--   This is Hoffman's error bound for a mixed system of linear inequalities and equations; the paper applies it to the linear system (3.20) to obtain the dual error bound (3.15).
--
--   **Formalization Note** "$\theta$ depending on $A$ and $C$ only" is encoded by choosing $\theta$ before $b$ and $d$. Nonemptiness of $S$ is an added, necessary hypothesis: for $S=\emptyset$ the page's distance is $+\infty$ and the inequality fails, whereas Lean's `Metric.infDist x ∅ = 0` would make it trivially true.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2282, Proposition 3.9 (cited from Facchinei–Pang [8])

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem prop_3_9 {n m k : ℕ} (A : E n →L[ℝ] E m) (C : E n →L[ℝ] E k) :
    ∃ θ > 0, ∀ (b : E m) (d : E k),
      {x : E n | (∀ i, A x i ≤ b i) ∧ C x = d}.Nonempty → ∀ xbar : E n,
        Metric.infDist xbar {x : E n | (∀ i, A x i ≤ b i) ∧ C x = d} ^ 2 ≤
          θ ^ 2 * (‖posPart (A xbar - b)‖ ^ 2 + ‖C xbar - d‖ ^ 2) := by sorry

end ProxADMMLC.Conv
