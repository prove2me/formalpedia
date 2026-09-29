-- Prove2me | Theorems.Thm_PhiDivRobust_Barrier_perspective_second_differential
-- name    : PhiDivRobust.Barrier.perspective_second_differential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:54:28.207802+00:00
-- url     : https://prove2.me/theorems/6f0b8972-690b-4dd4-a3e4-240cbbd27417
-- title:
--   Eq. (37) — the second differential of the perspective y f(s/y)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be three times continuously differentiable on $(0,\infty)$ and let $g(s,y)=y f(s/y)$. For all $s>0$, $y>0$ and every direction $h=(h_1,h_2)\in\mathbb R^2$,
--
--   $$\nabla^2 g(s,y)[h,h]\;=\;h^{\mathsf T}\nabla^2 g(s,y)h\;=\;f''(s/y)\left(\frac{h_1^2}{y}-\frac{2sh_1h_2}{y^2}+\frac{s^2h_2^2}{y^3}\right).$$
--
--   The bracket equals $(h_1-(s/y)h_2)^2/y\ge 0$, so the formula shows in particular that the perspective of a convex function is convex on the quadrant. It is the quadratic form against which the third differential is compared in (36).
--
--   **Formalization Note** The second differential is `iteratedFDeriv ℝ 2 g (s, y)` applied to $(h,h)$, and $f''$ is `iteratedDeriv 2 f`. $C^3$ regularity of $f$ on $(0,\infty)$ is the standing hypothesis of Theorem 2 made explicit (the page uses $f'''$ and requires the barrier to be $C^3$); $C^2$ would suffice for this identity.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, proof of Theorem 2, Eq. (37)

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

theorem perspective_second_differential (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
        (h.1 ^ 2 / y - 2 * s * h.1 * h.2 / y ^ 2 + s ^ 2 * h.2 ^ 2 / y ^ 3) := by sorry

end PhiDivRobust.Barrier
