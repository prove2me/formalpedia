-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_4_7
-- name    : TRSHolderKL.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:37.050338+00:00
-- url     : https://prove2.me/theorems/26c058c4-4a03-434d-a1d4-d9776fb32b27
-- title:
--   Lemma 4.7 — KL inequality with exponent 3/4 in hard case 2 (i)
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) and $b\in\mathbb R^n$, suppose $\lambda_1<0$ and the TRS is in hard case 2 (i), and let $x^*$ be an optimal solution. Then there are $\tau>0$ and $\epsilon>0$ such that
--   $$
--   \big(f(x)-f^*+\delta_B(x)\big)^{3/4}\le\tau\,\operatorname{dist}\big(-\nabla f(x),N_B(x)\big)\qquad\text{for all }x\in B(x^*,\epsilon).
--   $$
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ B(x*, ε), with δ_B(x) on the left and dist(−∇f(x), N_B(x)) on the right → for all x with ‖x‖ ≤ 1 and ‖x − x*‖ ≤ ε, δ_B dropped; N_B(x) is the normal cone {v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B} and dist is Metric.infDist; reason: for ‖x‖ > 1 the left side is +∞ and N_B(x) = ∅, so the right side is +∞ by the paper's convention dist(·, ∅) = ∞ (p.2) and the inequality is trivial; on the ball the cone formula is the normal cone and contains 0
--   - encoding: λ*, the Lagrange multiplier in the case definitions of Table 1 → some x* ∈ S₀ and λ* satisfy the KKT conditions of p.4; reason: for λ₁ < 0 the multiplier is the same for every optimal solution, so this is the table's λ*
--   - reading: x*, "an optimal solution to the TRS (P0)" fixed on p.15 before the lemma → every x* ∈ S₀ (universally quantified; τ and ε may depend on x*); reason: the paper fixes an arbitrary optimal solution; the claim is made for each one
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 4.7, display (42), p.18 (proof pp.18–21 and Appendix 7.3)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_grad
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_HardCase2i

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 4.7 (KL inequality for the hard case 2 (i)), Jiang and Li, arXiv:1911.11955v2,
display (42), p.18. Suppose `λ₁ < 0`. In hard case 2 (i), for an optimal solution `x*` there
are `τ > 0` and `ε > 0` with `(f(x) − f* + δ_B(x))^{3/4} ≤ τ dist(−∇f(x), N_B(x))` for all
`x ∈ B(x*, ε)`.

**Formalization Note.** `λ₁ < 0` is part of `HardCase2i`. `x*` ranges over `S₀`. Stated for
`‖x‖ ≤ 1`; for `‖x‖ > 1` both sides are `+∞`. `N_B(x)` is the published `FirstOrderOpt.ConvexTheory.normalCone` of the closed unit ball
(`{v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B}`) and `dist(−∇f(x), N_B(x))` is `Metric.infDist`; `∇f` is `grad`. -/
theorem lemma_4_7 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hcase : HardCase2i A b)
    (xstar : E n) (hxstar : xstar ∈ S0 A b) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : E n, ‖x‖ ≤ 1 → ‖x - xstar‖ ≤ ε →
      (f A b x - fstar A b) ^ ((3 : ℝ) / 4) ≤
        τ * Metric.infDist (-grad A b x) (FirstOrderOpt.ConvexTheory.normalCone (Metric.closedBall 0 1) x) := by sorry

end TRSHolderKL
