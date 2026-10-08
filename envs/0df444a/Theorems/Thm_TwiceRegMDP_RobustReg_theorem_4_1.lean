-- Prove2me | Theorems.Thm_TwiceRegMDP_RobustReg_theorem_4_1
-- name    : TwiceRegMDP.RobustReg.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:46:35.59815+00:00
-- url     : https://prove2.me/theorems/011c4ec6-b5cd-4ae1-b8ed-a4cab6560485
-- title:
--   Theorem 4.1 — the robust value function is the optimal solution of the twice regularized convex program (2)
-- statement:
--   Consider a finite discounted MDP with discount factor $\gamma\in(0,1)$, a strictly positive initial distribution $0<\mu_0\in\Delta_{\mathcal S}$, a nominal transition kernel $P_0$ and a nominal reward $r_0\in\mathbb R^{\mathcal X}$, where $\mathcal X = \mathcal S\times\mathcal A$. For every state $s$ let $\mathcal P_s\subseteq\mathbb R^{\mathcal X}$ and $\mathcal R_s\subseteq\mathbb R^{\mathcal A}$ be nonempty compact sets such that every perturbed transition is a kernel: $P_0(\cdot\mid s,a)+P_s(\cdot,a)\in\Delta_{\mathcal S}$ for all $P_s\in\mathcal P_s$ and $a\in\mathcal A$. Let $\mathcal U = (P_0+\mathcal P)\times(r_0+\mathcal R)$ be the s-rectangular uncertainty set. Then, for every policy $\pi\in\Delta_{\mathcal A}^{\mathcal S}$, the robust Bellman operator $T^{\pi,\mathcal U}$ has a unique fixed point $v^{\pi,\mathcal U}$, and $v^{\pi,\mathcal U}$ is the optimal solution of the convex program
--   $$\max_{v\in\mathbb R^{\mathcal S}}\ \langle v,\mu_0\rangle\quad\text{s.t.}\quad v(s)\le T^\pi_{(P_0,r_0)}v(s)-\sigma_{\mathcal R_s}(-\pi_s)-\sigma_{\mathcal P_s}(-\gamma v\cdot\pi_s)\ \text{ for all }s\in\mathcal S, \tag{2}$$
--   where $[v\cdot\pi_s](s',a) := v(s')\pi_s(a)$.
--
--   The robust value function under simultaneous reward and transition uncertainty is therefore the value of a *twice regularized* problem with the nominal model: the reward uncertainty yields a policy regularizer $\sigma_{\mathcal R_s}(-\pi_s)$, and the transition uncertainty a regularizer $\sigma_{\mathcal P_s}(-\gamma v\cdot\pi_s)$ that depends on both the policy and the value.
--
--   **Formalization Note.** The robust value function is the fixed point of $T^{\pi,\mathcal U}$, with existence and uniqueness in the conclusion (the page defines $v^{\pi,\mathcal U}(s) = \min_{(P,r)\in\mathcal U}v^\pi_{(P,r)}(s)$ and identifies it with this fixed point, citing the rectangular-case literature; the paper's proof uses the fixed-point property only). "The optimal solution" means feasible, objective-maximal, and the unique maximizer. The kernel condition on $P_0+\mathcal P$ is the p. 4 standing assumption that uncertain transitions lie in $\Delta_{\mathcal S}^{\mathcal X}$; nonemptiness and compactness make every minimum and support function attained. "Convex" in the source's statement is descriptive and is not asserted.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 6, Theorem 4.1, eq. (2) (proof in App. B.1, pp. 20–21)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- Theorem 4.1, general robust MDP (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 6). For the
s-rectangular uncertainty set `U = (P₀ + 𝒫) × (r₀ + ℛ)` around a nominal kernel `P₀` and reward
`r₀`, with every `𝒫_s ⊆ ℝ^{S×A}` and `ℛ_s ⊆ ℝ^A` nonempty and compact and every perturbed
transition `P₀(·|s,a) + P_s(·, a)` a probability distribution, and any policy `π`, the robust
operator `T^{π,U}` has a unique fixed point `v^{π,U}`, and it is the optimal solution of
`max ⟨v, μ₀⟩ s.t. v(s) ≤ T^π_{(P₀,r₀)} v(s) − σ_{ℛ_s}(−π_s) − σ_{𝒫_s}(−γ v · π_s) for all s`,
where `[v · π_s](s', a) = v(s') π_s(a)`. -/
theorem theorem_4_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (Pset : S → Set (S × A → ℝ)) (hPne : ∀ s, (Pset s).Nonempty) (hPc : ∀ s, IsCompact (Pset s))
    (hPker : ∀ s, ∀ Pp ∈ Pset s, ∀ a : A, (fun s' => P₀ s a s' + Pp (s', a)) ∈ stdSimplex ℝ S)
    (Rset : S → Set (A → ℝ)) (hRne : ∀ s, (Rset s).Nonempty) (hRc : ∀ s, IsCompact (Rset s))
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (rectUncertainty P₀ r₀ Pset Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (rectUncertainty P₀ r₀ Pset Rset) π v = v →
      IsOptimalSolution μ₀
        {w : S → ℝ | ∀ s, w s ≤ evalOp γ P₀ r₀ π w s - supportFn (Rset s) (-(π s))
            - supportFn (Pset s) (-(γ • vDotPi w π s))} v := by sorry

end TwiceRegMDP.RobustReg
