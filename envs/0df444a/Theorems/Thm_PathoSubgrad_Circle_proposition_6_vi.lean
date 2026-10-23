-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_vi
-- name    : PathoSubgrad.Circle.proposition_6_vi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:42.483775+00:00
-- url     : https://prove2.me/theorems/1a9c7abf-7fd6-4455-94f1-aee7c40e841c
-- title:
--   Proposition 6 (vi), p. 7 — f is Whitney C^∞ stratifiable
-- statement:
--   Let $\psi$ be any bump profile, $i_0\ge2$, and $f$ the function (4) of the example on the circle. Then $f$ is Whitney $C^\infty$-stratifiable: its graph $\{(x,f(x)):x\in\mathbb R^2\}\subseteq\mathbb R^3$ admits a locally finite partition into connected $C^\infty$ submanifolds satisfying the frontier condition and Whitney's condition A (Definition 5).
--
--   Whitney stratifiability is the standard tame-geometry hypothesis under which subgradient dynamics are usually analysed; the example satisfies it and still exhibits non-convergence.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (vi)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_vi (Ψ : BumpProfile) (i0 : ℕ) (hi0 : 2 ≤ i0) :
    IsWhitneyCInfStratifiable (fCirc Ψ i0) := by sorry

end PathoSubgrad.Circle
