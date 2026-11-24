-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_Supplement_theorem_2_iii
-- name    : SelfDualLP.Regularity.Supplement.theorem_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:18:59.027731+00:00
-- url     : https://prove2.me/theorems/ad409bab-d943-4691-b8b7-d1d890a7e037
-- title:
--   Theorem 2 (iii), corrected — (HLP) has an optimal solution; its optimal set is bounded in (x, τ, θ, s, κ), and bounded in full iff Aᵀd = 0, bᵀd = 0 forces d = 0
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ be arbitrary, let $x^0,s^0\in\mathbb R^n$ have positive coordinates and let $y^0\in\mathbb R^m$ be arbitrary. Let (HLP) be the homogeneous program of Ye, Todd and Mizuno: minimize $((x^0)^Ts^0+1)\theta$ over points $(y,x,\tau,\theta,s,\kappa)$ satisfying the constraints (1)–(4), with $y$ and $\theta$ free, $x\ge0$, $\tau\ge0$, and $s\ge0$, $\kappa\ge0$ the slacks of (2) and (3). An optimal solution is a feasible point minimizing the objective over the whole feasible set $\mathcal F_h$.
--
--   **Theorem 2 (iii), corrected.**
--
--   1. (HLP) has an optimal solution.
--   2. There is $R$ such that every optimal solution satisfies $|x_j|,|\tau|,|\theta|,|s_j|,|\kappa|\le R$.
--   3. The whole optimal solution set, including the free block $y$, is bounded if and only if
--   $$\forall d\in\mathbb R^m:\quad A^Td=0\ \text{ and }\ b^Td=0\ \Longrightarrow\ d=0 .$$
--
--   The paper states "(HLP) has an optimal solution and its optimal solution set is bounded" with no condition on $A$ and $b$. That is false as printed: if $d\neq0$ has $A^Td=0$ and $b^Td=0$, then $y\mapsto y+td$ preserves every constraint and the objective, so the optimal set is unbounded in $y$. For example, $m=n=1$, $A=0$, $b=0$, $c=0$, $x^0=s^0=1$, $y^0=0$ gives the optimal solutions $(t,1,1,0,0,0)$ for every real $t$. The statement above is the exact repair: existence and the boundedness of $(x,\tau,\theta,s,\kappa)$ hold unconditionally, and the paper's boundedness of the full set holds exactly when the kernel condition holds (for example, when $A$ has full row rank).
--
--   **Formalization Note** Boundedness is stated coordinatewise, by a common bound $R$ on the absolute values of the coordinates (the sup norm), which is equivalent to boundedness in any norm on the finite-dimensional space. The positivity of $x^0$ and $s^0$ is the paper's standing assumption on p. 56; the initial points are not specialized to the choice (7).
--
--   Differences from the source:
--
--   - correction: "its optimal solution set is bounded" (unconditional) → the coordinates x, τ, θ, s, κ of optimal solutions are bounded unconditionally, and the whole optimal set (with y) is bounded if and only if Aᵀd = 0, bᵀd = 0 imply d = 0; reason: the printed claim is false whenever this kernel is nonzero (counterexample A = 0, b = 0, c = 0, m = n = 1), because y is free and the paper states no rank condition
--   - encoding: "bounded" → a common bound R on the absolute values of all listed coordinates; reason: equivalent to norm-boundedness in finite dimension
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 57, Theorem 2 (iii); DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_HLP

open Matrix

namespace SelfDualLP.Regularity.Supplement

open SelfDualLP.Regularity

/-- **Theorem 2 (iii), corrected** (Ye–Todd–Mizuno 1994, p. 57). For arbitrary data `A, b, c`
and initial points `x⁰ > 0`, `s⁰ > 0`, `y⁰`, (HLP) has an optimal solution; on its optimal
solution set the coordinates `x, τ, θ, s, κ` are bounded; and the whole optimal solution set
`(y, x, τ, θ, s, κ)` is bounded **if and only if** the only `d` with `Aᵀd = 0` and `bᵀd = 0`
is `d = 0`.

The paper states "(HLP) has an optimal solution and its optimal solution set is bounded"
with no condition. Because `y` is free, any `d ≠ 0` with `Aᵀd = 0`, `bᵀd = 0` can be added
to the `y` of an optimal solution without changing feasibility or objective, so the printed
boundedness fails for such data (e.g. `m = n = 1`, `A = 0`, `b = 0`, `c = 0`,
`x⁰ = s⁰ = 1`, `y⁰ = 0`: every `(t, 1, 1, 0, 0, 0)` is optimal). The third conjunct
is the exact repair. Boundedness is coordinatewise in absolute value (the sup norm). -/
theorem theorem_2_iii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    (∃ w, IsHLPOptimal A b c x₀ y₀ s₀ w) ∧
    (∃ R : ℝ, ∀ w, IsHLPOptimal A b c x₀ y₀ s₀ w →
      (∀ j, |w.x j| ≤ R) ∧ |w.τ| ≤ R ∧ |w.θ| ≤ R ∧ (∀ j, |w.s j| ≤ R) ∧ |w.κ| ≤ R) ∧
    ((∃ R : ℝ, ∀ w, IsHLPOptimal A b c x₀ y₀ s₀ w →
        (∀ i, |w.y i| ≤ R) ∧ (∀ j, |w.x j| ≤ R) ∧ |w.τ| ≤ R ∧ |w.θ| ≤ R ∧
        (∀ j, |w.s j| ≤ R) ∧ |w.κ| ≤ R) ↔
      ∀ d : Fin m → ℝ, Aᵀ *ᵥ d = 0 → b ⬝ᵥ d = 0 → d = 0) := by sorry

end SelfDualLP.Regularity.Supplement
