-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_lemma_7_eq5
-- name    : PathoSubgrad.Circle.lemma_7_eq5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:36.713142+00:00
-- url     : https://prove2.me/theorems/aa56d9bb-a194-4ec2-b168-d253299dc74d
-- title:
--   Lemma 7, (5), p. 7 — for i large enough, ‖v_i − (−1)^i x_i/‖x_i‖‖ ≤ 6/log i
-- statement:
--   Let $x_i$ and $v_i=-(x_{i+1}-x_i)/\|x_{i+1}-x_i\|$ be as in the example on the circle. For $i$ large enough,
--   $$\Bigl\|v_i-(-1)^i\frac{x_i}{\|x_i\|}\Bigr\|\le\frac{6}{\log i}.$$
--
--   The step direction $v_i$ is thus asymptotically radial, pointing alternately outward and inward. This estimate controls the gradient of $f$ on the transition annuli around the $x_i$ and is used for Proposition 6 (iii) and (vii).
--
--   **Formalization Note.** "For $i$ large enough" is $\exists N,\ \forall i\ge N$.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Lemma 7, (5)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem lemma_7_eq5 : ∃ N : ℕ, ∀ i ≥ N,
    ‖vs i - (-1 : ℝ) ^ i • (‖xs i‖⁻¹ • xs i)‖ ≤ 6 / Real.log i := by sorry

end PathoSubgrad.Circle
