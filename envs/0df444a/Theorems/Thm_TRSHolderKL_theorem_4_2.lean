-- Prove2me | Theorems.Thm_TRSHolderKL_theorem_4_2
-- name    : TRSHolderKL.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:04.679169+00:00
-- url     : https://prove2.me/theorems/f772c3c5-854b-4c6d-b0ac-fb631e94718c
-- title:
--   Theorem 4.2 — global KL inequality for the convex TRS
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) with smallest eigenvalue $\lambda_1\ge0$, and $b\in\mathbb R^n$. Then there is $\tau>0$ such that
--   $$
--   \big(f(x)-f^*+\delta_B(x)\big)^{1-\rho}\le\tau\,\operatorname{dist}\big(-\nabla f(x),N_B(x)\big)\qquad\text{for all }x\in\mathbb R^n,
--   $$
--   where $\rho=1/4$ if $\lambda_1=0$, $b\in\mathrm{Range}(A)$ and $\|A^\dagger b\|=1$, and $\rho=1/2$ otherwise. Here $N_B(x)$ is the normal cone of the unit ball $B$ at $x$.
--
--   So the convex TRS satisfies the KL inequality globally, with exponent $3/4$ in the TRS-ill case and $1/2$ otherwise.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ ℝⁿ, with δ_B(x) on the left and dist(−∇f(x), N_B(x)) on the right → for all x with ‖x‖ ≤ 1, δ_B dropped; N_B(x) is the normal cone {v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B} and dist is Metric.infDist; reason: for ‖x‖ > 1 the left side is +∞ and N_B(x) = ∅, so the right side is +∞ by the paper's convention dist(·, ∅) = ∞ (p.2) and the inequality is trivial; on the ball the cone formula is the normal cone and contains 0
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Theorem 4.2, display (25), p.14

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_grad
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_xtilde

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

open Classical in
/-- Theorem 4.2, Jiang and Li, arXiv:1911.11955v2, display (25), p.14. For the TRS (P₀) with
`λ₁ ≥ 0` there is `τ > 0` with `(f(x) − f* + δ_B(x))^{1−ρ} ≤ τ dist(−∇f(x), N_B(x))` for all
`x ∈ ℝⁿ`, where `ρ = 1/4` if `λ₁ = 0`, `b ∈ Range(A)` and `‖A†b‖ = 1`, and `ρ = 1/2` otherwise.

**Formalization Note.** Stated for `‖x‖ ≤ 1`, where `δ_B(x) = 0` and `N_B(x)` is nonempty;
for `‖x‖ > 1` both sides are `+∞` (`N_B(x) = ∅` and `dist(·, ∅) = ∞` by the paper's
convention). `A†b` is `xtilde A b`. `N_B(x)` is the published `FirstOrderOpt.ConvexTheory.normalCone` of the closed unit ball
(`{v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B}`) and `dist(−∇f(x), N_B(x))` is `Metric.infDist`; `∇f` is `grad`. -/
theorem theorem_4_2 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hlam : 0 ≤ lam1 A) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n, ‖x‖ ≤ 1 →
      (f A b x - fstar A b) ^
          (1 - (if lam1 A = 0 ∧ b ∈ LinearMap.range (Matrix.toEuclideanLin A) ∧
                  ‖xtilde A b‖ = 1 then (1 : ℝ) / 4 else 1 / 2)) ≤
        τ * Metric.infDist (-grad A b x) (FirstOrderOpt.ConvexTheory.normalCone (Metric.closedBall 0 1) x) := by sorry

end TRSHolderKL
