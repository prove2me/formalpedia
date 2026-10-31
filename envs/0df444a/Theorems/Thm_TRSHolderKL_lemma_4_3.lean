-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_4_3
-- name    : TRSHolderKL.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:49.251787+00:00
-- url     : https://prove2.me/theorems/c249f98d-604a-46d0-b6f4-99b7189febe0
-- title:
--   Lemma 4.3 — KL inequality with exponent 1/2 at interior points, $\lambda_1<0$
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) with $\lambda_1<0$, $b\in\mathbb R^n$, and let $x^*$ be an optimal solution of (P$_0$). Then there are $\tau>0$ and $\epsilon>0$ such that
--   $$
--   \big(f(x)-f^*+\delta_B(x)\big)^{1/2}\le\tau\,\operatorname{dist}\big(-\nabla f(x),N_B(x)\big)\qquad\text{for all }x\in B(x^*,\epsilon)\cap\{x:\|x\|<1\},
--   $$
--   where $B(x^*,\epsilon)=\{x:\|x-x^*\|\le\epsilon\}$.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: δ_B(x) and N_B(x) for x with ‖x‖ < 1 → δ_B dropped; N_B(x) is the normal cone {v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B} and dist is Metric.infDist; reason: inside the ball δ_B = 0 and the cone formula is the normal cone
--   - reading: x*, "an optimal solution to the TRS (P0)" fixed on p.15 before the lemma → every x* ∈ S₀ (universally quantified; τ and ε may depend on x*); reason: the paper fixes an arbitrary optimal solution; the claim is made for each one
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 4.3, p.15

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_grad
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 4.3, Jiang and Li, arXiv:1911.11955v2, p.15. Suppose `λ₁ < 0` and let `x*` be an
optimal solution of (P₀). Then there are `τ > 0` and `ε > 0` with
`(f(x) − f* + δ_B(x))^{1/2} ≤ τ dist(−∇f(x), N_B(x))` for all `x ∈ B(x*, ε) ∩ {‖x‖ < 1}`.

**Formalization Note.** `x*` ranges over all of `S₀` (fixed on p.15: "Let x* be an optimal
solution"); `τ` and `ε` may depend on it. `B(x*, ε)` is the closed ball. `N_B(x)` is the published `FirstOrderOpt.ConvexTheory.normalCone` of the closed unit ball
(`{v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B}`) and `dist(−∇f(x), N_B(x))` is `Metric.infDist`; `∇f` is `grad`. -/
theorem lemma_4_3 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hlam : lam1 A < 0) (xstar : E n) (hxstar : xstar ∈ S0 A b) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : E n, ‖x - xstar‖ ≤ ε → ‖x‖ < 1 →
      (f A b x - fstar A b) ^ ((1 : ℝ) / 2) ≤
        τ * Metric.infDist (-grad A b x) (FirstOrderOpt.ConvexTheory.normalCone (Metric.closedBall 0 1) x) := by sorry

end TRSHolderKL
