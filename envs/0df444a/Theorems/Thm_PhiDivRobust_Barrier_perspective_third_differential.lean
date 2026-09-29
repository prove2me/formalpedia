-- Prove2me | Theorems.Thm_PhiDivRobust_Barrier_perspective_third_differential
-- name    : PhiDivRobust.Barrier.perspective_third_differential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:55:21.518608+00:00
-- url     : https://prove2.me/theorems/cbc695ef-8539-431b-8c76-8b29e92e6d0c
-- title:
--   Proof of Theorem 2 — the third differential of the perspective y f(s/y)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be three times continuously differentiable on $(0,\infty)$ and let $g(s,y)=y f(s/y)$. For all $s>0$, $y>0$ and every $h=(h_1,h_2)\in\mathbb R^2$,
--
--   $$\nabla^3 g(s,y)[h,h,h]=f''(s/y)\left(-\frac{3h_1^2h_2}{y^2}+\frac{6sh_1h_2^2}{y^3}-\frac{3s^2h_2^3}{y^4}\right)+f'''(s/y)\left(\frac{h_1^3}{y^2}-\frac{3sh_1^2h_2}{y^3}+\frac{3s^2h_1h_2^2}{y^4}-\frac{s^3h_2^3}{y^5}\right).$$
--
--   Together with Eq. (37) this expresses the third differential of the perspective through $f''$ and $f'''$ at the single point $s/y$; the bound (36) is read off from it.
--
--   **Formalization Note** The paper prints the last term as $s^3h_x^3/y^5$; $h_x$ is not a defined symbol and the identity holds exactly with $h_2$ (the $f'''$ bracket is $(h_1-(s/y)h_2)^3/y^2$), so the corrected term is stated. The third differential is `iteratedFDeriv ℝ 3 g (s, y)` applied to $(h,h,h)$; $f'',f'''$ are `iteratedDeriv 2 f`, `iteratedDeriv 3 f`.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, proof of Theorem 2, display after Eq. (37) (printed term s³h_x³/y⁵ corrected to s³h₂³/y⁵)

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

theorem perspective_third_differential (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
          (-(3 * h.1 ^ 2 * h.2 / y ^ 2) + 6 * s * h.1 * h.2 ^ 2 / y ^ 3
            - 3 * s ^ 2 * h.2 ^ 3 / y ^ 4)
        + iteratedDeriv 3 f (s / y) *
          (h.1 ^ 3 / y ^ 2 - 3 * s * h.1 ^ 2 * h.2 / y ^ 3 + 3 * s ^ 2 * h.1 * h.2 ^ 2 / y ^ 4
            - s ^ 3 * h.2 ^ 3 / y ^ 5) := by sorry

end PhiDivRobust.Barrier
