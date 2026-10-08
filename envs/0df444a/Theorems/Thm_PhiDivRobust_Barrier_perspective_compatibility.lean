-- Prove2me | Theorems.Thm_PhiDivRobust_Barrier_perspective_compatibility
-- name    : PhiDivRobust.Barrier.perspective_compatibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:55:49.405985+00:00
-- url     : https://prove2.me/theorems/6def4350-a586-41e7-9696-cbc0bde74b2f
-- title:
--   Proof of Theorem 2 — (36) holds with β = 3 + κ√2
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be convex and three times continuously differentiable on $(0,\infty)$, let $\kappa>0$, and suppose that condition (33) holds:
--
--   $$|f'''(s)|\le\kappa\,\frac{f''(s)}{s}\qquad\text{for all } s>0.$$
--
--   Let $g(s,y)=yf(s/y)$. Then for all $s>0$, $y>0$ and every $h=(h_1,h_2)\in\mathbb R^2$,
--
--   $$\bigl|\nabla^3 g(s,y)[h,h,h]\bigr|\;\le\;(3+\kappa\sqrt2)\;h^{\mathsf T}\nabla^2 g(s,y)h\;\sqrt{\frac{h_1^2}{s^2}+\frac{h_2^2}{y^2}}.$$
--
--   This is inequality (36) with $\beta=3+\kappa\sqrt2$: the third differential of the perspective is controlled by its second differential times the local norm of $h$ induced by the barrier $-\ln s-\ln y$ of the quadrant. Fed into den Hertog's Lemma A.2 it yields Theorem 2.
--
--   **Formalization Note** Differentials are `iteratedFDeriv`; $f'',f'''$ are `iteratedDeriv 2 f`, `iteratedDeriv 3 f`. $C^3$ regularity of $f$ on $(0,\infty)$ is the implicit standing hypothesis of Theorem 2 made explicit.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, pp. 350–351, proof of Theorem 2, chain of inequalities ending 'This proves that (36) holds for β = 3 + κ√2'

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

theorem perspective_compatibility (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s)
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
      (3 + κ * Real.sqrt 2) * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
        Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2) := by sorry

end PhiDivRobust.Barrier
