-- Prove2me | Theorems.Thm_RobustPower_StochGap_eq_2_9_2_10_doubled_solution_robust_feasible
-- name    : RobustPower.StochGap.eq_2_9_2_10_doubled_solution_robust_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:14:49.553114+00:00
-- url     : https://prove2.me/theorems/f5c6e638-8854-4b94-91e7-dc620453348c
-- title:
--   Eqs. (2.9)–(2.10) — doubling a solution for the central scenario covers every scenario
-- statement:
--   Let $b:\Omega\to\mathbb R^m_+$ and suppose the uncertainty set $I_b(\Omega)=\{b(\omega):\omega\in\Omega\}$ is symmetric about $b(\omega^0)$. Let $x$ lie in the first-stage domain (nonnegative, integer on the coordinates $I_1$) and $y\in\mathbb R^{n_2}_+$ satisfy $Ax+By\ge b(\omega^0)$. Then $b(\omega)\le 2b(\omega^0)$ for every $\omega$, and hence
--   $$A(2x)+B(2y)\ \ge\ 2b(\omega^0)\ \ge\ b(\omega)\qquad\forall\omega\in\Omega,$$
--   so $(2x,2y)$ is feasible for the robust problem $\Pi_{\mathrm{Rob}}(b)$ with continuous second stage.
--
--   This is the feasibility half of the proof of Theorem 2.1: integrality of the first stage survives doubling, which is why integer first-stage variables are allowed.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 13, Eqs. (2.9)–(2.10)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

open Matrix

namespace RobustPower.StochGap

/-- Eqs. (2.9)–(2.10) (p. 13): if the uncertainty set `I_b(Ω) = range b ⊆ ℝᵐ₊` is symmetric about
`b(ω⁰)` and `(x, y)` (with `x` in the first-stage domain and `y ≥ 0`) is feasible for scenario
`ω⁰`, then `(2x, 2y)` is feasible for the robust problem `Π_Rob(b)` with continuous second
stage. -/
theorem eq_2_9_2_10_doubled_solution_robust_feasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (I₁ : Set (Fin n₁)) (ω₀ : Ω)
    (hsym : IsSymmetricAbout (Set.range b) (b ω₀))
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (hx : x ∈ mixedIntDomain I₁) (hy : 0 ≤ y)
    (hfeas : b ω₀ ≤ A *ᵥ x + B *ᵥ y) :
    (∀ ω, b ω ≤ (2 : ℝ) • b ω₀) ∧
      RobFeasible A B b I₁ ∅ ((2 : ℝ) • x) ((2 : ℝ) • y) := by sorry

end RobustPower.StochGap
