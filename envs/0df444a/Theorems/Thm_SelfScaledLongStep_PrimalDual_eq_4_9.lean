-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_eq_4_9
-- name    : SelfScaledLongStep.PrimalDual.eq_4_9
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T12:56:39.591555+00:00
-- url     : https://prove2.me/theorems/2d63bd77-28e5-465a-991e-d3fc8f078626
-- title:
--   (4.9), p. 17 — for p ∈ K: F(x + αp) ≤ F(x) + α⟨F′(x), p⟩ + (α²/2)‖p‖²_x for all α ≥ 0
-- statement:
--   Let $K\subseteq E=\mathbb R^n$ be a proper cone with a $\nu$-self-scaled barrier $F$ ($\nu\ge1$). Let $x\in\operatorname{int}K$ and $p\in K$. Then for every $\alpha\ge0$,
--   $$F(x+\alpha p)\le F(x)+\alpha\langle F'(x),p\rangle+\frac{\alpha^2}{2}\,\|p\|_x^2,\qquad(4.9)$$
--   where $\|p\|_x=\langle F''(x)p,p\rangle^{1/2}$.
--
--   This is the form of Theorem 4.2 (4.8) in the degenerate case $\sigma_x(-p)=0$ (i.e. $-(-p)=p\in K$): the paper notes that the argument of Theorem 4.1 for $\sigma_x(p)=0$ gives $F''(x+\beta p)\preceq F''(x)$ for all $\beta\ge0$, and integrating twice along the ray yields (4.9). The step $x+\alpha p$ stays in $\operatorname{int}K$ for every $\alpha\ge0$.
--
--   **Formalization note.** Same setting and conventions as `SelfScaledLongStep.PrimalDual.theorem_4_2`: $E=E^*=\mathbb R^n$ via the inner product, $F'(x)$ is `gradient F x`, $\|p\|_x$ is `lnorm F x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 17, inequality (4.9) (the case σ_x(p) = 0 of Theorem 4.2)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **(4.9)** (p. 17), the `σ_x(−p) = 0` companion of Theorem 4.2: for `x ∈ int K`, `p ∈ K`
and every `α ≥ 0`,
`F(x + αp) ≤ F(x) + α⟨F'(x), p⟩ + (α²/2)‖p‖²_x`. -/
theorem eq_4_9 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hp : p ∈ K)
    (α : ℝ) (hα0 : 0 ≤ α) :
    F (x + α • p) ≤ F x + α * ⟪gradient F x, p⟫_ℝ + α ^ 2 / 2 * (lnorm F x p) ^ 2 := by sorry

end SelfScaledLongStep.PrimalDual
