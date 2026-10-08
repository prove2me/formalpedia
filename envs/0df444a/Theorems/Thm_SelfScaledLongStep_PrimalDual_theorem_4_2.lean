-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_2
-- name    : SelfScaledLongStep.PrimalDual.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:59.844804+00:00
-- url     : https://prove2.me/theorems/2d876a85-77b6-4cde-bc58-d68c0c21a3f8
-- title:
--   Theorem 4.2, p. 17 — F(x − αp) ≤ F(x) − α⟨F′(x), p⟩ + (‖p‖²_x/σ²_x(p))(−ασ_x(p) − ln(1 − ασ_x(p)))
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$, let $x\in\operatorname{int}K$ and $p\in E$ with $\sigma_x(p)>0$, and write $\|p\|_x=\langle F''(x)p,p\rangle^{1/2}$. Then for every $\alpha\in[0,1/\sigma_x(p))$,
--   $$F(x-\alpha p)\le F(x)-\alpha\langle F'(x),p\rangle+\frac{\|p\|_x^2}{\sigma_x^2(p)}\big(-\alpha\sigma_x(p)-\ln(1-\alpha\sigma_x(p))\big).\qquad(4.8)$$
--
--   This upper bound on the barrier along a long step is the basic estimate behind the potential-reduction and primal-dual analyses of the paper.
--
--   **Formalization Note** The step range is $0\le\alpha$, $\alpha\sigma_x(p)<1$; the hypothesis $\sigma_x(p)>0$ is printed in the theorem. $\|p\|_x$ is the published `lnorm F x p` and $\sigma_x$ the published `sigma K x`. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 17, Theorem 4.2, (4.8)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 4.2** (p. 17). Let `x ∈ int K` and `p ∈ E` with `σ_x(p) > 0`. Then for every
`α ∈ [0, 1/σ_x(p))`, (4.8):
`F(x − αp) ≤ F(x) − α⟨F'(x), p⟩ + (‖p‖²_x/σ_x²(p)) (−ασ_x(p) − ln(1 − ασ_x(p)))`,
with `‖p‖_x = ⟨F''(x)p, p⟩^{1/2}` (`lnorm F x p`). -/
theorem theorem_4_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hσ : 0 < sigma K x p)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α * sigma K x p < 1) :
    F (x - α • p) ≤ F x - α * ⟪gradient F x, p⟫_ℝ +
      (lnorm F x p) ^ 2 / (sigma K x p) ^ 2 *
        (-(α * sigma K x p) - Real.log (1 - α * sigma K x p)) := by sorry

end SelfScaledLongStep.PrimalDual
