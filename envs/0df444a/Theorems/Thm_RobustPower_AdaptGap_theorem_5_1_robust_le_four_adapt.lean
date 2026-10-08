-- Prove2me | Theorems.Thm_RobustPower_AdaptGap_theorem_5_1_robust_le_four_adapt
-- name    : RobustPower.AdaptGap.theorem_5_1_robust_le_four_adapt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:26.619344+00:00
-- url     : https://prove2.me/theorems/8ce3e1f2-8286-40ab-9a83-0a053d01b75a
-- title:
--   Theorem 5.1 — the adaptability gap is at most four
-- statement:
--   Let $A\in\mathbb R^{m\times n_1}$ and $B\in\mathbb R^{m\times n_2}$. Let $c\in\mathbb R_+^{n_1}$, and let every scenario $\omega\in\Omega$ have $b(\omega)\in\mathbb R_+^m$ and $d(\omega)\in\mathbb R_+^{n_2}$. Both decision stages may have designated nonnegative integer coordinates. If the paired uncertainty set $I_{(b,d)}(\Omega)=\{(b(\omega),d(\omega)):\omega\in\Omega\}$ is symmetric, then the optimal static robust cost is at most four times the optimal fully adaptive worst-case cost:
--
--   $$z_{\mathrm{Rob}}(b,d)\le4z_{\mathrm{Adapt}}(b,d).$$
--
--   This is the paper's constant-factor bound when uncertainty affects both right-hand sides and second-stage costs, including mixed-integer second-stage decisions.
--
--   **Formalization Note** Both values are extended-real infima over exactly the feasible decisions in (1.5)–(1.6); no optimal-solution attainment is assumed. Symmetry makes the scenario set nonempty and bounded. Integer coordinates are designated by sets, equivalent to the paper's product domains up to coordinate relabelling.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 28, Theorem 5.1

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems

namespace RobustPower.AdaptGap

/-- Theorem 5.1, p. 28: the adaptability gap is at most four. -/
theorem theorem_5_1_robust_le_four_adapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hsym : RobustPower.StochGap.IsSymmetric (scenarioSet b d)) :
    zRob A B b c d I₁ I₂ ≤ (4 : EReal) * zAdapt A B b c d I₁ I₂ := by sorry

end RobustPower.AdaptGap
