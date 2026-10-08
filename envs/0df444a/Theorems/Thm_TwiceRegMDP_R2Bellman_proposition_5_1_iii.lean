-- Prove2me | Theorems.Thm_TwiceRegMDP_R2Bellman_proposition_5_1_iii
-- name    : TwiceRegMDP.R2Bellman.proposition_5_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:40:44.777095+00:00
-- url     : https://prove2.me/theorems/9c86a78e-2b16-4861-b8db-5e003991fd8c
-- title:
--   Proposition 5.1 (iii) — the R² Bellman operators are $(1-\epsilon_*)$-contractions in $\|\cdot\|_\infty$
-- statement:
--   Consider a finite discounted MDP with nonempty state and action sets, nominal kernel $P_0$, nominal reward $r_0$, discount $\gamma\in(0,1)$, and nonnegative radii $\alpha^r_s,\alpha^P_s$, and suppose Assumption 5.1 holds with witnesses $\epsilon_s>0$. Let $\epsilon_*=\min_{s\in\mathcal S}\epsilon_s$. Then $\epsilon_*>0$, and for every policy $\pi$ and all $v_1,v_2\in\mathbb R^{\mathcal S}$,
--   $$\|T^{\pi,\mathrm R^2}v_1-T^{\pi,\mathrm R^2}v_2\|_\infty\le(1-\epsilon_*)\|v_1-v_2\|_\infty,\qquad \|T^{*,\mathrm R^2}v_1-T^{*,\mathrm R^2}v_2\|_\infty\le(1-\epsilon_*)\|v_1-v_2\|_\infty .$$
--
--   The contraction makes both operators admit unique fixed points by Banach's theorem, which is what defines the R² value functions of Definition 5.2. The modulus is $1-\epsilon_*$ rather than $\gamma$ because the value regularizer is itself Lipschitz in $v$.
--
--   **Formalization Note.** $\|\cdot\|_\infty$ is Mathlib's norm on `S → ℝ` (the sup norm); the norms inside the operators and in Assumption 5.1 are $\ell_2$-norms (`l2norm`). The full Assumption 5.1 is assumed as printed, although only its first bound is needed.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 8, Proposition 5.1 (iii); proof in App. C.1, pp. 23–24

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP
import Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops

namespace TwiceRegMDP.R2Bellman

/-- Proposition 5.1 (iii), contraction (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 8).
Under Assumption 5.1 (with witnesses `ϵ`), `ϵ_∗ := min_s ϵ_s > 0`, and for every policy `π` and
all `v₁ v₂`, `‖T^{π,R²} v₁ − T^{π,R²} v₂‖_∞ ≤ (1 − ϵ_∗) ‖v₁ − v₂‖_∞` and
`‖T^{∗,R²} v₁ − T^{∗,R²} v₂‖_∞ ≤ (1 − ϵ_∗) ‖v₁ − v₂‖_∞`. Here `‖·‖` on `S → ℝ` is Mathlib's
sup norm, i.e. `‖·‖_∞`. -/
theorem proposition_5_1_iii {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    0 < epsStar ϵ ∧
    ∀ v₁ v₂ : S → ℝ,
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        ‖evalOpR2 γ P₀ r₀ αr αP π v₁ - evalOpR2 γ P₀ r₀ αr αP π v₂‖ ≤
          (1 - epsStar ϵ) * ‖v₁ - v₂‖) ∧
      ‖optOpR2 γ P₀ r₀ αr αP v₁ - optOpR2 γ P₀ r₀ αr αP v₂‖ ≤
        (1 - epsStar ϵ) * ‖v₁ - v₂‖ := by sorry

end TwiceRegMDP.R2Bellman
