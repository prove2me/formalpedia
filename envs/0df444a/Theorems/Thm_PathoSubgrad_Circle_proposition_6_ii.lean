-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_proposition_6_ii
-- name    : PathoSubgrad.Circle.proposition_6_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:37.824988+00:00
-- url     : https://prove2.me/theorems/54809354-4157-4ab6-acfa-43b21b9acf3a
-- title:
--   Proposition 6 (ii), p. 7 — for i0 large, ∇f = v_i on B_{1/2^i}(x_i), so (x_i) is a subgradient sequence with steps ε_i
-- statement:
--   Let $\psi$ be any bump profile. For every sufficiently large $i_0$, the function $f$ of (4) satisfies (3):
--   $$\nabla f(y)=v_i\qquad\text{for all } i\ge i_0 \text{ and } y\in B_{1/2^i}(x_i),$$
--   and consequently the sequence $x_{i_0},x_{i_0+1},\dots$ is a subgradient sequence of $f$ (Definition 1) with step sizes $\varepsilon_{i_0},\varepsilon_{i_0+1},\dots$.
--
--   This is the defining property of the construction: the gradient of $f$ at each $x_i$ is exactly the step direction $v_i$, so the prescribed sequence is a run of the small-step subgradient method.
--
--   **Formalization Note.** The paper states "Let $i_0\ge2$". For small $i_0$ the supports of the bumps overlap (numerically, $\|x_3-x_5\|\approx0.259<1/4+1/16$, so $\psi_3$ does not vanish on $B_{1/32}(x_5)$), and (3) can fail; the statement therefore reads $\exists N,\ \forall i_0\ge N$, with $N$ allowed to depend on the bump. Balls are open. The subgradient sequence is indexed from $0$: its $k$-th term is $x_{i_0+k}$ with step $\varepsilon_{i_0+k}$.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 7, Proposition 6 (ii), with (3) on p. 6

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem proposition_6_ii (Ψ : BumpProfile) : ∃ N : ℕ, ∀ i0 ≥ N,
    (∀ i ≥ i0, ∀ y ∈ Metric.ball (xs i) (((2 : ℝ) ^ i)⁻¹),
      HasGradientAt (fCirc Ψ i0) (vs i) y) ∧
    IsSubgradientSeq (fCirc Ψ i0) (fun k => eps (i0 + k)) (fun k => xs (i0 + k)) := by sorry

end PathoSubgrad.Circle
