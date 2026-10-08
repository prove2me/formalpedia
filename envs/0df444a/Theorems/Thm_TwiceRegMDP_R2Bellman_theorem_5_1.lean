-- Prove2me | Theorems.Thm_TwiceRegMDP_R2Bellman_theorem_5_1
-- name    : TwiceRegMDP.R2Bellman.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:40:56.178866+00:00
-- url     : https://prove2.me/theorems/1b9f757d-4f25-4be4-ba55-656f83618c11
-- title:
--   Theorem 5.1 — the greedy policy of the R² optimal value is the unique optimal R² policy
-- statement:
--   Consider a finite discounted MDP with nonempty state and action sets, nominal kernel $P_0$, nominal reward $r_0$, discount $\gamma\in(0,1)$, nonnegative radii $\alpha^r_s,\alpha^P_s$, and suppose Assumption 5.1 holds with witnesses $\epsilon_s>0$. Then:
--
--   1. the R² optimality operator $T^{*,\mathrm R^2}$ has a unique fixed point $v^{*,\mathrm R^2}$, the **R² optimal value function**;
--   2. for every policy $\pi$, the R² evaluation operator $T^{\pi,\mathrm R^2}$ has a unique fixed point $v^{\pi,\mathrm R^2}$, the **R² value function** of $\pi$;
--   3. a greedy policy $\pi^{*,\mathrm R^2}$ for $v^{*,\mathrm R^2}$ (one with $T^{\pi^{*},\mathrm R^2}v^{*,\mathrm R^2}=T^{*,\mathrm R^2}v^{*,\mathrm R^2}$) exists; every such policy satisfies, for all $\pi\in\Delta^{\mathcal S}_{\mathcal A}$,
--   $$v^{\pi^{*,\mathrm R^2},\mathrm R^2}=v^{*,\mathrm R^2}\ \ge\ v^{\pi,\mathrm R^2};$$
--   and every policy whose R² value equals $v^{*,\mathrm R^2}$ (that is, every optimal R² policy) is greedy for $v^{*,\mathrm R^2}$;
--   4. if moreover $\alpha^r_s>0$ for every state $s$, the greedy policy for $v^{*,\mathrm R^2}$ is unique, hence it is the unique optimal R² policy.
--
--   This is the R² analogue of the fundamental theorem of discounted dynamic programming: acting greedily with respect to the R² optimal value yields an optimal policy, which is what justifies the R² modified policy iteration algorithm.
--
--   **Formalization Note.** Assumption 5.1 is not in the theorem's sentence on p. 8, but its proof (p. 24) assumes it, and without it the fixed points need not exist. Uniqueness (clause 4) needs a positive weight in the regularizer: with $|\mathcal S|=1$, two actions, $r_0\equiv0$ and $\alpha^r=\alpha^P=0$ every policy is greedy and optimal; $\alpha^r_s>0$ is assumed for clause 4 only. The existence and uniqueness of the fixed points (clauses 1–2) are stated so that the value functions of Definition 5.2 are well defined. Norms inside the operators are $\ell_2$-norms; the inequality $\ge$ is pointwise.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 8, Theorem 5.1 and Definition 5.2; proof in App. C.2, p. 24

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP
import Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops

namespace TwiceRegMDP.R2Bellman

/-- Theorem 5.1, R² optimal policy (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 8; proof App. C.2,
p. 24). Under Assumption 5.1 (with witnesses `ϵ`; the proof assumes it):
1. `T^{∗,R²}` has a unique fixed point `v^{∗,R²}` (Definition 5.2 (ii) is well posed);
2. for every policy `π`, `T^{π,R²}` has a unique fixed point `v^{π,R²}` (Definition 5.2 (i));
3. a greedy policy for `v^{∗,R²}` exists; every greedy policy `π^∗` has `v^{π^∗,R²} = v^{∗,R²}`;
   every policy has `v^{π,R²} ≤ v^{∗,R²}`; and every policy whose R² value equals `v^{∗,R²}`
   (i.e. every optimal policy) is greedy for `v^{∗,R²}`;
4. if moreover `α^r_s > 0` for every `s`, the greedy policy for `v^{∗,R²}` is unique, so it is the
   unique optimal R² policy. -/
theorem theorem_5_1 {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    ∃ vstar : S → ℝ,
      optOpR2 γ P₀ r₀ αr αP vstar = vstar ∧
      (∀ v : S → ℝ, optOpR2 γ P₀ r₀ αr αP v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π → ∃! v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v) ∧
      (∃ π : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      (∀ πstar : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar πstar →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP πstar v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v ≤ vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        (∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v = vstar) →
        IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      ((∀ s, 0 < αr s) →
        ∀ π₁ π₂ : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π₁ →
          IsGreedy γ P₀ r₀ αr αP vstar π₂ → π₁ = π₂) := by sorry

end TwiceRegMDP.R2Bellman
