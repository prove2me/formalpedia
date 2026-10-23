-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_i
-- name    : PathoSubgrad.Circle.proposition_6_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:35.117986+00:00
-- url     : https://prove2.me/theorems/3833f072-2b4d-480a-9819-b167b5d547d5
-- title:
--   Proposition 6 (i), p. 7 — f is C^∞ away from the unit circle and the origin
-- statement:
--   Let $\psi$ be any bump profile, $i_0\ge2$, and $f$ the function (4) of the example on the circle. Then $f$ is $C^\infty$ on
--   $$\mathbb R^2\setminus\bigl(S^1\cup\{0\}\bigr).$$
--
--   Away from the circle only finitely many bumps $\psi_i$ are active near any point, so $f$ is locally a finite combination of smooth functions. This is the smoothness half of the stratification of the graph of $f$.
--
--   **Formalization Note.** The paper states (i) on $\mathbb R^2\setminus S^1$. Near the origin $f=\varphi=1-\|x\|$, which is not differentiable at $0$, and item (iv) puts $0$ in $\operatorname{crit}f$; the paper's own proof (p. 8) says the pieces are $C^\infty$ on $\mathbb R^2\setminus(S^1\cup\{0\})$. The statement is on that corrected set.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (i) (domain corrected per the proof, p. 8)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_i (Ψ : BumpProfile) (i0 : ℕ) (hi0 : 2 ≤ i0) :
    ContDiffOn ℝ ∞ (fCirc Ψ i0) {x | ‖x‖ ≠ 1 ∧ x ≠ 0} := by sorry

end PathoSubgrad.Circle
