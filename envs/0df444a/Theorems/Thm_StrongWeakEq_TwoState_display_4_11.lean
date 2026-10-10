-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_display_4_11
-- name    : StrongWeakEq.TwoState.display_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:57.716011+00:00
-- url     : https://prove2.me/theorems/cf916bd1-43df-4f1b-b0ff-bf068ab9d9ad
-- title:
--   (4.11), p. 13 — at Q* ∼ (5/12, 7/12), Γ₁ is maximized uniquely at a* and argmax_{b≥0} Γ₂(b) = [0, 7/12]
-- statement:
--   In Example 4.3 ($\lambda=\tfrac12$, $\rho=1$, $\rho'=2$, $g_1(a)=-a^2$, the piecewise $g_2$), let $Q^*\sim(a^*,b^*)=(5/12,7/12)$. For the first-row candidate $(-a,a)$ and the second-row candidate $(b,-b)$, $a,b\ge0$:
--   1. $\Gamma^{(a^*,b^*)}_1(a)=-a^2+\tfrac56a$;
--   2. $\Gamma^{(a^*,b^*)}_1(a)<\Gamma^{(a^*,b^*)}_1(a^*)$ for every $a\ge0$, $a\ne a^*$;
--   3. $\Gamma^{(a^*,b^*)}_2(b)=g_2(b)-\tfrac56b$;
--   4. the set of maximizers over $b\ge0$ is an interval:
--   $$
--   \operatorname*{arg\,max}_{b\ge0}\Gamma^{(a^*,b^*)}_2(b)=[0,7/12]. \tag{4.11}
--   $$
--
--   With Theorem 3.1 this shows that $Q^*$ is a weak equilibrium, while the non-unique maximizer $b^*=7/12$ makes Proposition 3.2 inapplicable.
--
--   **Formalization Note** State 1 is `0 : Fin 2`, state 2 is `1 : Fin 2`. $\Gamma_1$ depends only on $a$ and $\Gamma_2$ only on $b$, so the statement quantifies over the rows `![-a, a]` and `![b, -b]` directly. The page's case formula for $b\ge7/12$ prints $-(b^2-7/12)+193/144$, a typo for $-(b-7/12)^2+193/144$; the Lean states $\Gamma_2=g_2(b)-\tfrac56b$ and the argmax, which need no case formula.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 13, Example 4.3, (4.11)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel
import Definitions.Def_StrongWeakEq_TwoState_Example43

namespace StrongWeakEq.TwoState

/-- (4.11), p. 13, Example 4.3: at `Q* ∼ (5/12, 7/12)`, `Γ₁(a) = −a² + (5/6)a` for the row
`(−a, a)`, maximized over `a ≥ 0` uniquely at `a* = 5/12`; `Γ₂(b) = g₂(b) − (5/6)b` for the row
`(b, −b)`, and `argmax_{b ≥ 0} Γ₂(b) = [0, 7/12]`. -/
theorem display_4_11 :
    (∀ a : ℝ, 0 ≤ a → StrongWeakEq.Existence.Gamma ex43 Qstar 0 ![-a, a] = -a ^ 2 + 5 / 6 * a) ∧
    (∀ a : ℝ, 0 ≤ a → a ≠ 5 / 12 →
      StrongWeakEq.Existence.Gamma ex43 Qstar 0 ![-a, a] < StrongWeakEq.Existence.Gamma ex43 Qstar 0 ![-(5 / 12), 5 / 12]) ∧
    (∀ b : ℝ, 0 ≤ b → StrongWeakEq.Existence.Gamma ex43 Qstar 1 ![b, -b] = ex43g₂ b - 5 / 6 * b) ∧
    {b : ℝ | 0 ≤ b ∧ ∀ b' : ℝ, 0 ≤ b' →
        StrongWeakEq.Existence.Gamma ex43 Qstar 1 ![b', -b'] ≤ StrongWeakEq.Existence.Gamma ex43 Qstar 1 ![b, -b]} = Set.Icc 0 (7 / 12) := by sorry

end StrongWeakEq.TwoState
