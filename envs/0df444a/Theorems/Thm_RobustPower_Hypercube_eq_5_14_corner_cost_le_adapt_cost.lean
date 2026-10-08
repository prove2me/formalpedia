-- Prove2me | Theorems.Thm_RobustPower_Hypercube_eq_5_14_corner_cost_le_adapt_cost
-- name    : RobustPower.Hypercube.eq_5_14_corner_cost_le_adapt_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:00.876216+00:00
-- url     : https://prove2.me/theorems/5b648b1c-42a0-4c6b-b835-ebbbe4f208b4
-- title:
--   Eq. (5.14) — the robust cost of $(x,y(\bar\omega))$ is at most the adaptive cost
-- statement:
--   In the setting of (5.6)–(5.7), with $d(\omega)\in\mathbb R^{n_2}_+$ for every scenario, let $\bar\omega\in\Omega$ satisfy $d(\omega)\le d(\bar\omega)$ entrywise for every $\omega\in\Omega$. If $(x,y(\cdot))$ is feasible for $\Pi_{\mathrm{Adapt}}(A,B,b,d)$, then
--
--   $$c^Tx+\sup_{\omega\in\Omega}d(\omega)^Ty(\bar\omega)\ \le\ c^Tx+\sup_{\omega\in\Omega}d(\omega)^Ty(\omega).$$
--
--   The left side is the worst-case cost in $\Pi_{\mathrm{Rob}}(A,B,b,d)$ of the static pair $(x,y(\bar\omega))$; the right side is the worst-case cost in $\Pi_{\mathrm{Adapt}}(A,B,b,d)$ of $(x,y(\cdot))$.
--
--   **Formalization Note** Both costs are extended reals; the inequality is in $[-\infty,+\infty]$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 32, Eq. (5.14) and the chain containing it

import Definitions.Def_RobustPower_Hypercube_Problems

namespace RobustPower.Hypercube

/-- Inequality (5.14) and the chain around it (p. 32): let `ω̄` be a scenario whose
cost vector `d(ω̄)` is entrywise maximal over `Ω`. For every feasible solution
`(x, y(·))` of `Π_Adapt(A,B,b,d)`, the worst-case cost of the static pair `(x, y(ω̄))`,
`cᵀx + max_ω d(ω)ᵀy(ω̄)`, is at most `cᵀx + max_ω d(ω)ᵀy(ω)`. -/
theorem eq_5_14_corner_cost_le_adapt_cost
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hd : ∀ ω, 0 ≤ d ω)
    (ωbar : Ω) (hdbar : ∀ ω j, d ω j ≤ d ωbar j)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ)
    (hxy : adaptFeasible A B b I₁ I₂ x y) :
    RobustPower.AdaptGap.robCost c d x (y ωbar) ≤ RobustPower.AdaptGap.adaptCost c d x y := by sorry

end RobustPower.Hypercube
