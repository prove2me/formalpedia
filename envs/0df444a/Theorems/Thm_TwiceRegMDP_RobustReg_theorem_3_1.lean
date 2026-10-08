-- Prove2me | Theorems.Thm_TwiceRegMDP_RobustReg_theorem_3_1
-- name    : TwiceRegMDP.RobustReg.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:46:03.499082+00:00
-- url     : https://prove2.me/theorems/daa68b32-5e02-41bc-9e7f-d4eb76a2d757
-- title:
--   Theorem 3.1 — reward-robust MDPs are regularized MDPs with regularizer $\sigma_{\mathcal R_s}(-\pi_s)$
-- statement:
--   Consider a finite discounted MDP with discount factor $\gamma\in(0,1)$, a strictly positive initial distribution $0<\mu_0\in\Delta_{\mathcal S}$, a nominal transition kernel $P_0$ and a nominal reward $r_0\in\mathbb R^{\mathcal X}$. For every state $s$ let $\mathcal R_s\subseteq\mathbb R^{\mathcal A}$ be nonempty and compact, and let $\mathcal U = \{P_0\}\times(r_0+\mathcal R)$ with $\mathcal R = \times_{s}\mathcal R_s$. Then, for every policy $\pi\in\Delta_{\mathcal A}^{\mathcal S}$, the robust Bellman operator $T^{\pi,\mathcal U}$ has a unique fixed point $v^{\pi,\mathcal U}$, and $v^{\pi,\mathcal U}$ is the optimal solution of
--   $$\max_{v\in\mathbb R^{\mathcal S}}\ \langle v,\mu_0\rangle\quad\text{s.t.}\quad v(s)\le T^\pi_{(P_0,r_0)}v(s)-\sigma_{\mathcal R_s}(-\pi_s)\ \text{ for all }s\in\mathcal S .$$
--
--   Thus a robust MDP with uncertain reward only is a regularized MDP whose policy regularizer is $\Omega_s(\pi_s) = \sigma_{\mathcal R_s}(-\pi_s)$: policy regularization is equivalent to reward uncertainty.
--
--   **Formalization Note.** The robust value function is the fixed point of $T^{\pi,\mathcal U}$, with existence and uniqueness in the conclusion; "the optimal solution" means feasible, objective-maximal and the unique maximizer. The reward uncertainty set is s-rectangular, as the paper's proof assumes ("By the rectangularity assumption, $\mathcal R = \times_{s\in\mathcal S}\mathcal R_s$", p. 16). Nonemptiness and compactness of each $\mathcal R_s$ make the minima and the support function attained.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 5, Theorem 3.1 (proof in App. A.2, p. 16)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- Theorem 3.1, reward-robust MDP (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 5). For
`U = {P₀} × (r₀ + ℛ)` with `ℛ = ×_s ℛ_s`, each `ℛ_s` nonempty and compact, `P₀` a kernel, and any
policy `π`, the robust operator `T^{π,U}` has a unique fixed point `v^{π,U}`, and it is the optimal
solution of `max ⟨v, μ₀⟩ s.t. v(s) ≤ T^π_{(P₀,r₀)} v(s) − σ_{ℛ_s}(−π_s) for all s`. -/
theorem theorem_3_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (Rset : S → Set (A → ℝ)) (hRne : ∀ s, (Rset s).Nonempty) (hRc : ∀ s, IsCompact (Rset s))
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (rewardUncertainty P₀ r₀ Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (rewardUncertainty P₀ r₀ Rset) π v = v →
      IsOptimalSolution μ₀
        {w : S → ℝ | ∀ s, w s ≤ evalOp γ P₀ r₀ π w s - supportFn (Rset s) (-(π s))} v := by sorry

end TwiceRegMDP.RobustReg
