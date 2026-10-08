-- Prove2me | Theorems.Thm_TwiceRegMDP_R2Bellman_proposition_5_1_i
-- name    : TwiceRegMDP.R2Bellman.proposition_5_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:40:35.842596+00:00
-- url     : https://prove2.me/theorems/4bc0dfe6-df28-4f61-8048-2797d26df705
-- title:
--   Proposition 5.1 (i) — monotonicity of the R² Bellman operators
-- statement:
--   Consider a finite discounted MDP with nonempty state and action sets, nominal kernel $P_0$, nominal reward $r_0$, discount $\gamma\in(0,1)$, and nonnegative radii $\alpha^r_s,\alpha^P_s$. Suppose Assumption 5.1 holds: there are $\epsilon_s>0$ with
--   $$\alpha^P_s\le\min\Big(\frac{1-\gamma-\epsilon_s}{\gamma\sqrt{|\mathcal S|}}\,;\ \min_{u\in\mathbb R^{\mathcal A}_+,\|u\|=1,\ w\in\mathbb R^{\mathcal S}_+,\|w\|=1}u^\top P_0(\cdot\mid s,\cdot)\,w\Big)\quad\text{for all } s.$$
--   Then for all $v_1,v_2\in\mathbb R^{\mathcal S}$ with $v_1\le v_2$ pointwise, and every policy $\pi\in\Delta^{\mathcal S}_{\mathcal A}$,
--   $$T^{\pi,\mathrm R^2}v_1\le T^{\pi,\mathrm R^2}v_2\qquad\text{and}\qquad T^{*,\mathrm R^2}v_1\le T^{*,\mathrm R^2}v_2 .$$
--
--   Monotonicity is not automatic here: the value regularizer $-\alpha^P_s\gamma\|\pi_s\|\|v\|$ decreases as $\|v\|$ grows, and the second bound of Assumption 5.1 is what keeps the operator monotone. It is the property used to compare R² values of different policies in Theorem 5.1.
--
--   **Formalization Note.** All norms here are $\ell_2$-norms (`l2norm`). The full Assumption 5.1 is assumed as printed, although only its second bound is needed. $\alpha^r_s,\alpha^P_s\ge0$ are the paper's ball radii.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 8, Proposition 5.1 (i); proof in App. C.1, pp. 22–23

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP
import Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops

namespace TwiceRegMDP.R2Bellman

/-- Proposition 5.1 (i), monotonicity (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 8).
Under Assumption 5.1 (with witnesses `ϵ`), for all `v₁ ≤ v₂` (pointwise) and every policy
`π ∈ Δ_A^S`, `T^{π,R²} v₁ ≤ T^{π,R²} v₂` and `T^{∗,R²} v₁ ≤ T^{∗,R²} v₂` (pointwise). -/
theorem proposition_5_1_i {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    ∀ v₁ v₂ : S → ℝ, v₁ ≤ v₂ →
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        evalOpR2 γ P₀ r₀ αr αP π v₁ ≤ evalOpR2 γ P₀ r₀ αr αP π v₂) ∧
      optOpR2 γ P₀ r₀ αr αP v₁ ≤ optOpR2 γ P₀ r₀ αr αP v₂ := by sorry

end TwiceRegMDP.R2Bellman
