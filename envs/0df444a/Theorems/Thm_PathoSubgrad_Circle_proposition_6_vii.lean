-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_vii
-- name    : PathoSubgrad.Circle.proposition_6_vii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:37.288966+00:00
-- url     : https://prove2.me/theorems/1b1b4d00-dbaa-4297-a76a-284324e7f3fd
-- title:
--   Proposition 6 (vii), p. 7 — for i0 large, ‖∇f(x)‖ > 1/2 for x ∉ crit f (a Kurdyka–Łojasiewicz inequality)
-- statement:
--   Let $\psi$ be any bump profile. If $i_0$ is large enough, the function $f$ of (4) satisfies a Kurdyka–Łojasiewicz inequality of the form
--   $$\|\nabla f(x)\|>\frac12\qquad\text{for all } x\in\mathbb R^2\setminus\operatorname{crit}f.$$
--
--   The gradient stays uniformly away from zero off the critical set, which is the strongest possible form of a Kurdyka–Łojasiewicz inequality; even so the subgradient sequence does not converge.
--
--   **Formalization Note.** Lean's `gradient` is $0$ at points of non-differentiability, so the statement also asserts that $f$ is differentiable at every non-critical point (true, since $\operatorname{crit}f=S^1\cup\{0\}$ and $f$ is smooth elsewhere). "Large enough" is $\exists N,\ \forall i_0\ge N$, with $N$ depending on the bump.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (vii)

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_vii (Ψ : BumpProfile) : ∃ N : ℕ, ∀ i0 ≥ N, ∀ x ∉ critSet (fCirc Ψ i0),
    DifferentiableAt ℝ (fCirc Ψ i0) x ∧ 1 / 2 < ‖gradient (fCirc Ψ i0) x‖ := by sorry

end PathoSubgrad.Circle
