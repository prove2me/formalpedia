-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_Supplement_theorem_5_i
-- name    : SelfDualLP.Regularity.Supplement.theorem_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:19:37.099677+00:00
-- url     : https://prove2.me/theorems/f7d471b8-9ed6-4588-9b6a-2da8aaafc644
-- title:
--   Theorem 5 (i), corrected — central points of (HLP) exist for every μ > 0, are unique up to y-shifts with Aᵀd = 0, bᵀd = 0, and unique iff that kernel is zero
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ be arbitrary and take the paper's choice (7): $y^0=0$, $x^0=s^0=e$. Then (HLP) minimizes $(n+1)\theta$ subject to (1)–(4) with $\bar b=b-Ae$, $\bar c=c-e$, $\bar z=c^Te+1$; let $\mathcal F_h^0$ be the set of its feasible points $(y,x,\tau,\theta,s,\kappa)$ with $x,\tau,s,\kappa$ strictly positive, where $s$ and $\kappa$ are the slacks of (2) and (3). Write $X=\operatorname{diag}(x)$.
--
--   **Theorem 5 (i), corrected.** For every $\mu>0$:
--
--   1. there is $w=(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h^0$ with
--   $$\begin{pmatrix}Xs\\ \tau\kappa\end{pmatrix}=\mu e; \qquad (10)$$
--   2. a point $v\in\mathcal F_h^0$ satisfies (10) if and only if it has the same $x,\tau,\theta,s,\kappa$ as $w$ and $A^T(v_y-w_y)=0$, $b^T(v_y-w_y)=0$;
--   3. the point satisfying (10) in $\mathcal F_h^0$ is unique if and only if $A^Td=0$ and $b^Td=0$ imply $d=0$.
--
--   The paper states that for every $\mu>0$ the tuple $(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h^0$ satisfying (10) is unique, with no condition on $A$ and $b$. That is false as printed when some $d\neq0$ has $A^Td=0$ and $b^Td=0$, because $y$ is free: for $m=n=1$, $A=0$, $b=0$, $c=0$, $\mu=1$, every $(t,1,1,1,1,1)$ lies in $\mathcal F_h^0$ and satisfies (10). The statement above is the exact repair: existence and the uniqueness of $(x,\tau,\theta,s,\kappa)$ hold unconditionally, and the paper's uniqueness of the full tuple holds exactly under the kernel condition (for example, when $A$ has full row rank). These points form the central path of (HLP), along which the algorithm of the paper moves.
--
--   **Formalization Note** The choice (7) is substituted into the published general (HLP) definitions ($x^0=s^0=$ the all-ones vector, $y^0=0$). Equation (10) is written componentwise: $x_js_j=\mu$ for every $j$ and $\tau\kappa=\mu$.
--
--   Differences from the source:
--
--   - correction: "there is a unique (y, x, τ, θ, s, κ) in 𝓕_h⁰" satisfying (10) → existence; uniqueness of x, τ, θ, s, κ; y unique up to adding d with Aᵀd = 0, bᵀd = 0; and uniqueness of the full tuple iff that kernel is zero; reason: the printed uniqueness is false whenever this kernel is nonzero (counterexample A = 0, b = 0, c = 0, m = n = 1, μ = 1), because y is free and the paper states no rank condition
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 59, Theorem 5 (i); DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_HLP

open Matrix

namespace SelfDualLP.Regularity.Supplement

open SelfDualLP.Regularity

/-- **Theorem 5 (i), corrected** (Ye–Todd–Mizuno 1994, p. 59), under the choice (7)
`y⁰ = 0`, `x⁰ = s⁰ = e`. For arbitrary data `A, b, c` and every `μ > 0` there is a point
`w = (y, x, τ, θ, s, κ)` of `Fₕ°` with `Xs = μe` and `τκ = μ` (equation (10)), and the set of
all such points is exactly `w` with `y` shifted by the vectors `d` with `Aᵀd = 0`, `bᵀd = 0`:
`x, τ, θ, s, κ` are unique, and the whole tuple is unique **if and only if** the only such
`d` is `d = 0`.

The paper states uniqueness of the whole tuple with no condition. Because `y` is free, it
fails when some `d ≠ 0` has `Aᵀd = 0` and `bᵀd = 0` (e.g. `m = n = 1`, `A = 0`, `b = 0`,
`c = 0`, `μ = 1`: every `(t, 1, 1, 1, 1, 1)` is in `Fₕ°` and satisfies (10)). -/
theorem theorem_5_i {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (hμ : 0 < μ) :
    (∃ w : HLPPoint m n,
      HLPStrictlyFeasible A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) w ∧
      (∀ j, w.x j * w.s j = μ) ∧ w.τ * w.κ = μ ∧
      ∀ v : HLPPoint m n,
        (HLPStrictlyFeasible A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) v ∧
          (∀ j, v.x j * v.s j = μ) ∧ v.τ * v.κ = μ) ↔
        (v.x = w.x ∧ v.τ = w.τ ∧ v.θ = w.θ ∧ v.s = w.s ∧ v.κ = w.κ ∧
          Aᵀ *ᵥ (v.y - w.y) = 0 ∧ b ⬝ᵥ (v.y - w.y) = 0)) ∧
    ((∃! w : HLPPoint m n,
      HLPStrictlyFeasible A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) w ∧
      (∀ j, w.x j * w.s j = μ) ∧ w.τ * w.κ = μ) ↔
      ∀ d : Fin m → ℝ, Aᵀ *ᵥ d = 0 → b ⬝ᵥ d = 0 → d = 0) := by sorry

end SelfDualLP.Regularity.Supplement
