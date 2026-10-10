-- Prove2me | Theorems.Thm_PowerOfDUniversality_Diffusion_theorem_2_4_uniqueness
-- name    : PowerOfDUniversality.Diffusion.theorem_2_4_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:47.256011+00:00
-- url     : https://prove2.me/theorems/5566d571-c35a-465a-916a-9003945ae703
-- title:
--   Theorem 2.4, uniqueness clause — the integral equations (2.4) with regulator $U_1$ have at most one solution
-- statement:
--   Let $\beta>0$ and $k\ge2$. Fix a real path $w$ (the Brownian path in Theorem 2.4) and an initial value $x\in\mathbb R^k$. Suppose $(\bar Q,U_1)$ and $(\bar Q',U_1')$ both solve the equations (2.4) driven by $w$ from $x$. Here a solution has càdlàg coordinates, $\bar Q_1\le0$, $\bar Q_i\equiv 0$ for $i\ge k+1$, and a nonnegative nondecreasing càdlàg regulator $U_1$ with $\int_0^\infty\mathbb 1_{[\bar Q_1(t)<0]}\,dU_1(t)=0$. Then
--   $$\bar Q(t)=\bar Q'(t)\quad\text{and}\quad U_1(t)=U_1'(t)\qquad\text{for all }t\ge0 .$$
--
--   This is the uniqueness half of Theorem 2.4: "$(\bar Q_1,\dots,\bar Q_k)$ are the unique solutions in $D_{\mathbb R^k}[0,\infty)$ of (2.4) … and $U_1$ is the unique nondecreasing nonnegative process … satisfying $\int_0^\infty\mathbb 1_{[\bar Q_1(t)<0]}dU_1(t)=0$". It makes the limit in Theorem 2.4 a well-defined functional of the Brownian motion and the initial value.
--
--   **Formalization Note** Uniqueness is stated pathwise and deterministically, for every path $w$. No regularity of $w$ is assumed: a solution can exist only when $w$ is càdlàg, because $w$ is then determined by $\bar Q$ and $U_1$. The constraint $\bar Q_1\le0$ is part of the solution concept (see the definition of (2.4)).
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 7–8, Theorem 2.4 (uniqueness clause, equations (2.4))

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_Limit

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-- **Theorem 2.4, uniqueness clause** (Mukherjee, Borst, van Leeuwaarden & Whiting,
arXiv:1612.00723v2, p. 8): for `β > 0` and `k ≥ 2`, the solution of (2.4) is pathwise unique.
For every driving path `w` and initial value `x ∈ ℝ^k`, any two pairs `(Q̄, U₁)`, `(Q̄′, U₁′)`
that solve (2.4) (`Solves24`, which includes `Q̄_1 ≤ 0` and the complementarity condition
`∫ 𝟙[Q̄_1 < 0] dU₁ = 0`) coincide at every time `t ≥ 0`. No regularity of `w` is assumed: a
solution can exist only when `w` is càdlàg. -/
theorem theorem_2_4_uniqueness (β : ℝ) (hβ : 0 < β) (k : ℕ) (hk : 2 ≤ k) (w : ℝ → ℝ)
    (x : Fin k → ℝ) (Q Q' : ℝ → ℕ → ℝ) (U U' : ℝ → ℝ)
    (h : Solves24 β k w x Q U) (h' : Solves24 β k w x Q' U') :
    ∀ t : ℝ, 0 ≤ t → Q t = Q' t ∧ U t = U' t := by sorry

end PowerOfDUniversality.Diffusion
