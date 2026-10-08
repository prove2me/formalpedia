-- Prove2me | Theorems.Thm_RobustPower_Hypercube_theorem_2_4_robust_eq_deterministic
-- name    : RobustPower.Hypercube.theorem_2_4_robust_eq_deterministic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:06.793366+00:00
-- url     : https://prove2.me/theorems/b6459810-a1ca-4629-b432-64ce2aaf2956
-- title:
--   Theorem 2.4 — $\Pi_{\mathrm{Rob}}(b)$ is the deterministic problem with the worst right-hand side
-- statement:
--   Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, let $I_1$ be the integer coordinates of the first stage, and let the second-stage variables be continuous ($p_2=0$). Let $\Omega$ be a nonempty scenario set with right-hand sides $b(\omega)\in\mathbb R^m_+$ that are bounded above, and let
--
--   $$b^h_j=\sup_{\omega\in\Omega} b_j(\omega),\qquad j=1,\dots,m.$$
--
--   Then:
--   1. a pair $(x,y)$ is feasible for the robust problem $\Pi_{\mathrm{Rob}}(b)$ (1.2) if and only if it is feasible for the deterministic problem $\Pi$: $Ax+By\ge b^h$, $x\in\mathbb R^{n_1-p_1}_+\times\mathbb Z^{p_1}_+$, $y\in\mathbb R^{n_2}_+$;
--   2. consequently $z_{\mathrm{Rob}}(b)=z(\Pi)$.
--
--   The robust problem, with one constraint block per scenario, is thus a single mixed integer program whose size does not depend on the uncertainty set. The same worst-scenario principle, applied to all the data at once, drives Theorem 5.4.
--
--   **Formalization Note** Values are extended-real infima, so the equality also covers infeasible problems. The paper's $\max$ is a supremum here; boundedness above of the right-hand sides replaces its attainment, so the statement contains the paper's case.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 17, Theorem 2.4

import Definitions.Def_RobustPower_Hypercube_RhsProblems

namespace RobustPower.Hypercube

/-- Theorem 2.4 (p. 17): with `bʰ` the coordinatewise maximum of the right-hand
sides, a pair `(x, y)` is feasible for `Π_Rob(b)` exactly when it is feasible for
the deterministic problem `Π` with right-hand side `bʰ`, and `z_Rob(b) = z(Π)`.
The second-stage variables are continuous (`p₂ = 0`, `I₂ = ∅`), as in `Π` on the page. -/
theorem theorem_2_4_robust_eq_deterministic
    {m n₁ n₂ : ℕ} {Ω : Type*} [Nonempty Ω]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁))
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : ∀ ω, 0 ≤ b ω)
    (hbdd : BddAbove (Set.range b)) :
    (∀ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
      robFeasibleRhs A B b I₁ ∅ x y ↔ detFeasible A B (worstRhs b) I₁ ∅ x y) ∧
    zRobRhs A B b I₁ ∅ c d = zDet A B (worstRhs b) I₁ ∅ c d := by sorry

end RobustPower.Hypercube
