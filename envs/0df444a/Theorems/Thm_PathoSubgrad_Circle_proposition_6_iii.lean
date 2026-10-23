-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_iii
-- name    : PathoSubgrad.Circle.proposition_6_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:37.697419+00:00
-- url     : https://prove2.me/theorems/b4e5dc28-952e-4194-9ae1-37dcf682dab9
-- title:
--   Proposition 6 (iii), p. 7 — on the unit circle, ∂^c f(p) = {ap : a ∈ [−1, 1]} = ∂^c φ(p)
-- statement:
--   Let $\psi$ be any bump profile, $i_0\ge2$, $f$ the function (4), and $\varphi(x)=|1-\|x\||$. For every point $p$ of the unit circle,
--   $$\partial^c f(p)=\{ap: a\in[-1,1]\}=\partial^c\varphi(p).$$
--
--   Although $f$ is wildly modified near the circle, its Clarke subdifferential on the circle is that of the distance function: the segment from $-p$ to $p$. In particular every point of $S^1$ is critical. This is the key input for path differentiability, the Whitney stratification and the identification of the critical set.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (iii)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_iii (Ψ : BumpProfile) (i0 : ℕ) (hi0 : 2 ≤ i0)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : ‖p‖ = 1) :
    clarkeSubdiff (fCirc Ψ i0) p = {w | ∃ a ∈ Set.Icc (-1 : ℝ) 1, w = a • p} ∧
    clarkeSubdiff phi p = {w | ∃ a ∈ Set.Icc (-1 : ℝ) 1, w = a • p} := by sorry

end PathoSubgrad.Circle
