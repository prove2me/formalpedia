-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_Supplement_theorem_2_i
-- name    : SelfDualLP.Regularity.Supplement.theorem_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:17:55.806957+00:00
-- url     : https://prove2.me/theorems/93eaeba4-d146-4376-b35c-2a3b4818ecd7
-- title:
--   Theorem 2 (i) — the LP dual (HLD) of (HLP) is (HLP) in the multipliers (y′, x′, τ′, θ′)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ be arbitrary, and let $x^0,s^0\in\mathbb R^n$ have positive coordinates and $y^0\in\mathbb R^m$ be arbitrary. Let (HLP) be the homogeneous program with objective $\min M\theta$, $M=(x^0)^Ts^0+1$, constraints (1)–(4), $y,\theta$ free and $x,\tau\ge0$, and let $\mathcal F_h$ be its feasible set of points $(y,x,\tau,\theta,s,\kappa)$, where $s$ and $\kappa$ are the slacks of (2) and (3). Let (HLD) be the linear-programming dual of (HLP), with multipliers $y',x',\tau',\theta'$ of the constraints (1), (2), (3), (4).
--
--   **Theorem 2 (i).** (HLD) has the same form as (HLP): it is (HLP) with $(y,x,\tau,\theta)$ replaced by $(y',x',\tau',\theta')$. Precisely:
--
--   1. reading a vector $(y,x,\tau,\theta)$ together with its slacks as a point of (HLP) is injective, the feasible vectors of the encoded (HLP) are mapped exactly onto $\mathcal F_h$, and the encoded cost is $M\theta$;
--   2. the feasible multipliers $(y',x',\tau',\theta')$ of (HLD), read in the same way, are mapped exactly onto $\mathcal F_h$;
--   3. the dual objective is $-M\theta'$, so
--   $$\max\ -M\theta' \ \text{ over (HLD)} \quad\text{is}\quad \min\ M\theta' \ \text{ over (HLP)},$$
--   and the optimal solutions of (HLD) are exactly the optimal points of (HLP);
--   4. written in the equivalent minimization form, the data of (HLD) (matrix, right-hand side, cost, row relations, sign conditions) are identical to those of (HLP).
--
--   This is the self-duality of (HLP): every primal-dual statement about (HLP) is a statement about a single program, which is why Theorem 2 (ii)–(v) and the algorithm can work in $\mathcal F_h$ alone.
--
--   **Formalization Note** (HLP) is encoded as a general-form linear program over $\mathbb R^{m+n+2}$ and (HLD) is computed from it by the published Table 4.1 dual operator, not written down by hand; the theorem identifies both with the published (HLP) feasibility predicate, objective and optimality notion of the base mission. The positivity of $x^0$ and $s^0$ is the paper's standing assumption on p. 56.
--
--   Differences from the source:
--
--   - encoding: (HLP) and (HLD) are linear programs in (y, x, τ, θ) and (y′, x′, τ′, θ′) → both are general-form LP data over Fin (m + n + 2), the blocks identified through a fixed equivalence, and (HLD) is the output of the general dual operator in its equivalent minimization form; reason: this computes the dual from the coefficients and sign conditions of (HLP) instead of assuming its shape
--   - reading: "(HLD) has the same form as (HLP), i.e., (HLD) is simply (HLP) with (y, x, τ, θ) being replaced by (y′, x′, τ′, θ′)" → the feasible sets of both programs map bijectively onto F_h, the raw dual objective is −((x⁰)ᵀs⁰ + 1)θ′, its maximizers are exactly the HLP-optimal points, and the minimization-form data coincide; reason: "same form" is made precise as equality of the optimization problems after the max/min sense conversion, since the raw objectives differ in sign
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 56, Theorem 2 (i); proof remark p. 57; DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_Supplement_HLD

open Matrix

namespace SelfDualLP.Regularity.Supplement

open SelfDualLP.Regularity LinearOptimization

/-- **Theorem 2 (i)** (Ye–Todd–Mizuno 1994, p. 56). For arbitrary data `A, b, c` and initial
points `x⁰ > 0`, `s⁰ > 0`, `y⁰`, the linear-programming dual (HLD) of (HLP) is (HLP) in the
multipliers `(y′, x′, τ′, θ′)`:
1. the general-form encoding `hlpLP` is (HLP): reading `v` as `(y, x, τ, θ)` with slacks
   is injective, and its image of the feasible set of `hlpLP` is `Fₕ`; its cost is
   `((x⁰)ᵀs⁰ + 1)θ`;
2. the image of the feasible set of (HLD) is again `Fₕ`;
3. the raw dual objective `max pᵀ(0,0,0,−(x⁰)ᵀs⁰−1)` equals `−((x⁰)ᵀs⁰ + 1)θ′`, so the
   optimal solutions of the maximization (HLD) are exactly the optimal points of (HLP);
4. in the equivalent minimization form, (HLD) is literally the data of (HLP). -/
theorem theorem_2_i {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    Function.Injective (toHLPPoint A b c x₀ y₀ s₀) ∧
    toHLPPoint A b c x₀ y₀ s₀ '' generalFeasibleSet (hlpLP A b c x₀ y₀ s₀) =
      {w | HLPFeasible A b c x₀ y₀ s₀ w} ∧
    (∀ v, (hlpLP A b c x₀ y₀ s₀).c ⬝ᵥ v = HLPObjective x₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ v)) ∧
    toHLPPoint A b c x₀ y₀ s₀ '' generalFeasibleSet (HLD A b c x₀ y₀ s₀) =
      {w | HLPFeasible A b c x₀ y₀ s₀ w} ∧
    (∀ p, p ⬝ᵥ (hlpLP A b c x₀ y₀ s₀).b =
      -HLPObjective x₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ p)) ∧
    (∀ p, IsLpDualOptimal (hlpLP A b c x₀ y₀ s₀).b
        (generalFeasibleSet (HLD A b c x₀ y₀ s₀)) p ↔
      IsHLPOptimal A b c x₀ y₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ p)) ∧
    HLD A b c x₀ y₀ s₀ = hlpLP A b c x₀ y₀ s₀ := by sorry

end SelfDualLP.Regularity.Supplement
