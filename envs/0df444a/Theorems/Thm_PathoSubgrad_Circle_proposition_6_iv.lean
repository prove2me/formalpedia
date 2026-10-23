-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_iv
-- name    : PathoSubgrad.Circle.proposition_6_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:42.423988+00:00
-- url     : https://prove2.me/theorems/c289e308-2289-4643-a21f-06327c439aa5
-- title:
--   Proposition 6 (iv), p. 7 — for i0 large, crit f = S¹ ∪ {0}
-- statement:
--   Let $\psi$ be any bump profile. For every sufficiently large $i_0$, the critical set of the function $f$ of (4) is
--   $$\operatorname{crit}f=S^1\cup\{0\},$$
--   where $\operatorname{crit}f=\{x:0\in\partial^c f(x)\}$ and $S^1$ is the unit circle.
--
--   The only critical points are the circle, around which the subgradient sequence accumulates, and the origin, where $f$ has a cone-shaped maximum. This identification is what makes the weak Sard condition and the Kurdyka–Łojasiewicz inequality checkable.
--
--   **Formalization Note.** The paper states the proposition for $i_0\ge2$ but its proof takes "$i_0$ large enough"; the statement reads $\exists N,\ \forall i_0\ge N$.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (iv) (proof on p. 9 takes i0 large enough)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_iv (Ψ : BumpProfile) : ∃ N : ℕ, ∀ i0 ≥ N,
    critSet (fCirc Ψ i0) = Metric.sphere 0 1 ∪ {0} := by sorry

end PathoSubgrad.Circle
