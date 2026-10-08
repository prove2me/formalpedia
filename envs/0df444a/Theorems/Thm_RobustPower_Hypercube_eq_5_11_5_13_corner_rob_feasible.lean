-- Prove2me | Theorems.Thm_RobustPower_Hypercube_eq_5_11_5_13_corner_rob_feasible
-- name    : RobustPower.Hypercube.eq_5_11_5_13_corner_rob_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:58.150421+00:00
-- url     : https://prove2.me/theorems/bbe15136-3dee-4e6d-952f-31989a2003ea
-- title:
--   Eqs. (5.11)–(5.13) — the adaptive decision at $\bar\omega$ is robust feasible
-- statement:
--   In the setting of (5.6)–(5.7), let $\bar\omega\in\Omega$ be a scenario with $A(\bar\omega)\le A(\omega)$, $B(\bar\omega)\le B(\omega)$ and $b(\omega)\le b(\bar\omega)$ entrywise for every $\omega\in\Omega$. If $(x,y(\cdot))$ is feasible for $\Pi_{\mathrm{Adapt}}(A,B,b,d)$, then the static pair $(x,y(\bar\omega))$ is feasible for $\Pi_{\mathrm{Rob}}(A,B,b,d)$: for every $\omega\in\Omega$,
--
--   $$A(\omega)x+B(\omega)y(\bar\omega)\ \ge\ A(\bar\omega)x+B(\bar\omega)y(\bar\omega)\ \ge\ b(\bar\omega)\ \ge\ b(\omega).$$
--
--   No sign is assumed on $A$, $B$ or $b$; the nonnegativity of $x$ and $y(\bar\omega)$ comes from the decision domains.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 32, Eqs. (5.11)–(5.13)

import Definitions.Def_RobustPower_Hypercube_Problems

namespace RobustPower.Hypercube

/-- Inequalities (5.11)–(5.13) (p. 32): let `ω̄` be a scenario whose `A(ω̄)`, `B(ω̄)`
are entrywise minimal and whose `b(ω̄)` is entrywise maximal over `Ω`. For every
feasible solution `(x, y(·))` of `Π_Adapt(A,B,b,d)`, the static pair `(x, y(ω̄))` is
feasible for `Π_Rob(A,B,b,d)`. -/
theorem eq_5_11_5_13_corner_rob_feasible
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (ωbar : Ω)
    (hA : ∀ ω i j, A ωbar i j ≤ A ω i j)
    (hB : ∀ ω i j, B ωbar i j ≤ B ω i j)
    (hb : ∀ ω i, b ω i ≤ b ωbar i)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ)
    (hxy : adaptFeasible A B b I₁ I₂ x y) :
    robFeasible A B b I₁ I₂ x (y ωbar) := by sorry

end RobustPower.Hypercube
