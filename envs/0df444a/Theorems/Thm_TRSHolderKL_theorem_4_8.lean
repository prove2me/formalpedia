-- Prove2me | Theorems.Thm_TRSHolderKL_theorem_4_8
-- name    : TRSHolderKL.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:32.550036+00:00
-- url     : https://prove2.me/theorems/f71d6ca2-8f9b-4c91-bb87-0b9d3d31f2d9
-- title:
--   Theorem 4.8 — KL inequality for the TRS at every optimal solution: exponent 3/4 in the TRS-ill case, 1/2 otherwise
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix with $n\ge2$, $b\in\mathbb R^n$, $f(x)=x^TAx-2b^Tx$, $B$ the unit ball, $S_0$ the optimal solution set of $\min\{f(x):\|x\|\le1\}$ and $f^*$ its optimal value. For every optimal solution $x^*\in S_0$ there are $\tau_{KL}>0$ and $\epsilon>0$ such that
--   $$
--   \big(f(x)-f^*+\delta_B(x)\big)^{\varrho}\le\tau_{KL}\,\operatorname{dist}\big(-\nabla f(x),N_B(x)\big)\qquad\text{for all }x\in B(x^*,\epsilon),
--   $$
--   where $B(x^*,\epsilon)=\{x:\|x-x^*\|\le\epsilon\}$, $N_B(x)$ is the normal cone of $B$ at $x$, and
--   $$
--   \varrho=\begin{cases}3/4,&\text{in the TRS-ill case (24): }\lambda_1\le0,\ b\in\mathrm{Range}(A-\lambda_1I),\ \|(A-\lambda_1I)^\dagger b\|=1,\\ 1/2,&\text{otherwise.}\end{cases}
--   $$
--
--   This is the main result of the paper: the KL inequality holds at every optimal solution of the (possibly nonconvex) TRS, and the KL exponent and the Hölderian error bound modulus of Theorem 3.13 always sum to one.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ B(x*, ε), with δ_B(x) on the left and dist(−∇f(x), N_B(x)) on the right → for all x with ‖x‖ ≤ 1 and ‖x − x*‖ ≤ ε, δ_B dropped; N_B(x) is the normal cone {v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B} and dist is Metric.infDist; reason: for ‖x‖ > 1 the left side is +∞ and N_B(x) = ∅, so the right side is +∞ by the paper's convention dist(·, ∅) = ∞ (p.2) and the inequality is trivial; on the ball the cone formula is the normal cone and contains 0
--   - reading: x*, "an optimal solution to the TRS (P0)" fixed on p.15 before the lemma → every x* ∈ S₀ (universally quantified; τ and ε may depend on x*); reason: the paper fixes an arbitrary optimal solution; the claim is made for each one
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Theorem 4.8, display (56), p.21

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_grad
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_TRSIll

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

open Classical in
/-- Theorem 4.8, Jiang and Li, arXiv:1911.11955v2, display (56), p.21. For every optimal
solution `x*` of the trust region subproblem (P₀) there are `τ_KL > 0` and `ε > 0` such that
the KL inequality `(f(x) − f* + δ_B(x))^ϱ ≤ τ_KL dist(−∇f(x), N_B(x))` holds for all
`x ∈ B(x*, ε)`, where `ϱ = 3/4` in the TRS-ill case (24) and `ϱ = 1/2` otherwise.

**Formalization Note.** `n ≥ 2`, `A` nonzero real symmetric, `b ∈ ℝⁿ` are the paper's blanket
assumptions (p.1); `x*` ranges over all of `S₀` (Section 4, p.15) and `τ_KL`, `ε` may depend
on it. `B(x*, ε)` is the closed ball. Stated for `‖x‖ ≤ 1`, where `δ_B(x) = 0` and
`N_B(x) ≠ ∅`; for `‖x‖ > 1` both sides are `+∞` (`dist(·, ∅) = ∞`, p.2). `N_B(x)` is the published `FirstOrderOpt.ConvexTheory.normalCone` of the closed unit ball
(`{v | ⟪v, y − x⟫ ≤ 0 ∀ y ∈ B}`) and `dist(−∇f(x), N_B(x))` is `Metric.infDist`; `∇f` is `grad`. -/
theorem theorem_4_8 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (xstar : E n) (hxstar : xstar ∈ S0 A b) :
    ∃ τKL : ℝ, 0 < τKL ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : E n, ‖x‖ ≤ 1 → ‖x - xstar‖ ≤ ε →
      (f A b x - fstar A b) ^ (if TRSIll A b then (3 : ℝ) / 4 else 1 / 2) ≤
        τKL * Metric.infDist (-grad A b x) (FirstOrderOpt.ConvexTheory.normalCone (Metric.closedBall 0 1) x) := by sorry

end TRSHolderKL
