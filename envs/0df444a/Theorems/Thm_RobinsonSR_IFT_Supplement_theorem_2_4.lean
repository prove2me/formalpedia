-- Prove2me | Theorems.Thm_RobinsonSR_IFT_Supplement_theorem_2_4
-- name    : RobinsonSR.IFT.Supplement.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:47:59.187172+00:00
-- url     : https://prove2.me/theorems/f362fddd-cd0f-4640-9f3d-250602d2b905
-- title:
--   Theorem 2.4, p. 48 — Banach perturbation lemma: T(A, a, ·)⁻¹ ∩ V is single-valued on W, Lipschitzian with modulus λ(1 − λ‖A − A₀‖)⁻¹
-- statement:
--   Let $X$ be a real Banach space, $a_0\in X'$, $C\subseteq X$ closed and convex, and $A_0\in L(X,X')$, the space of bounded linear operators from $X$ to $X'$. Suppose $x_0\in X$ satisfies the generalized equation
--   $$0\in A_0x+a_0+\partial\psi_C(x). \tag{2.9}$$
--   If (2.9) is strongly regular at $x_0$ with associated Lipschitz modulus $\lambda$, then there are neighbourhoods $M$ of $A_0$ in $L(X,X')$ (operator norm), $N$ of $a_0$ and $W$ of the origin in $X'$, and $V$ of $x_0$, such that, writing
--   $$T(A,a,x):=Ax+a+\partial\psi_C(x),$$
--   for every $A\in M$ and $a\in N$:
--
--   1. $\lambda\|A-A_0\|<1$;
--   2. for every $y\in W$ there is exactly one $x\in V$ with $y\in T(A,a,x)$;
--   3. if $y_1,y_2\in W$ and $x_1,x_2\in V$ satisfy $y_i\in T(A,a,x_i)$, then
--   $$\|x_1-x_2\|\le\lambda\,(1-\lambda\|A-A_0\|)^{-1}\|y_1-y_2\|.$$
--
--   So $T(A,a,\cdot)^{-1}\cap V$ is a single-valued function on $W$, Lipschitzian with modulus $\lambda(1-\lambda\|A-A_0\|)^{-1}$. This extends Banach's perturbation lemma for invertible linear operators to linear generalized equations.
--
--   **Formalization Note** Item 1 is not printed in the statement; the modulus $\lambda(1-\lambda\|A-A_0\|)^{-1}$ is meaningful only when it holds, and the paper's proof secures it in its step (1) when choosing $M$. Including it makes the conclusion stronger, not weaker. Strong regularity of (2.9) is strong regularity with $f(x)=A_0x+a_0$, so $f(x_0)=A_0x_0+a_0$ and $f'(x_0)=A_0$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 48, Theorem 2.4, (2.9)

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT.Supplement

open scoped Topology

/-- Robinson 1980, Theorem 2.4 (p. 48): a Banach perturbation lemma for linear generalized
equations. If `0 ∈ A₀x + a₀ + ∂ψ_C(x)` (2.9) is strongly regular at `x₀` with modulus `λ`, then
for `A` near `A₀` and `a` near `a₀`, `T(A, a, ·)⁻¹ ∩ V` is single-valued on a neighbourhood `W`
of the origin and Lipschitzian there with modulus `λ(1 − λ‖A − A₀‖)⁻¹`. -/
theorem theorem_2_4 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (a0 : StrongDual ℝ X) (C : Set X) (hC : IsClosed C) (hCc : Convex ℝ C)
    (A0 : X →L[ℝ] StrongDual ℝ X) (x0 : X)
    (hsol : -(A0 x0 + a0) ∈ normalCone C x0)
    (lam : ℝ) (hreg : StronglyRegular C (A0 x0 + a0) A0 x0 lam) :
    ∃ M ∈ 𝓝 A0, ∃ N ∈ 𝓝 a0, ∃ W ∈ 𝓝 (0 : StrongDual ℝ X), ∃ V ∈ 𝓝 x0,
      ∀ A ∈ M, ∀ a ∈ N,
        lam * ‖A - A0‖ < 1 ∧
        (∀ y ∈ W, ∃! x, x ∈ V ∧ y - (A x + a) ∈ normalCone C x) ∧
        ∀ y₁ ∈ W, ∀ y₂ ∈ W, ∀ x₁ ∈ V, ∀ x₂ ∈ V,
          y₁ - (A x₁ + a) ∈ normalCone C x₁ → y₂ - (A x₂ + a) ∈ normalCone C x₂ →
          ‖x₁ - x₂‖ ≤ lam * (1 - lam * ‖A - A0‖)⁻¹ * ‖y₁ - y₂‖ := by sorry

end RobinsonSR.IFT.Supplement
