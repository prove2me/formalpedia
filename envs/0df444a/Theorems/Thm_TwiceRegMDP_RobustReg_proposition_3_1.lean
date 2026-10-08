-- Prove2me | Theorems.Thm_TwiceRegMDP_RobustReg_proposition_3_1
-- name    : TwiceRegMDP.RobustReg.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:46:06.785268+00:00
-- url     : https://prove2.me/theorems/97777e99-ab4b-4c37-8450-9a8114047add
-- title:
--   Proposition 3.1 — the robust value function is the optimal solution of the robust program $(P_{\mathcal U})$
-- statement:
--   Consider a finite discounted MDP with discount factor $\gamma\in(0,1)$ and a strictly positive initial distribution $0<\mu_0\in\Delta_{\mathcal S}$. Let $\mathcal U := \mathcal P\times\mathcal R$ be the uncertainty set of a robust MDP, where $\mathcal P$ is a nonempty compact set of transition kernels and $\mathcal R\subseteq\mathbb R^{\mathcal X}$ is a nonempty compact set of rewards (neither need be rectangular), and let $\pi\in\Delta_{\mathcal A}^{\mathcal S}$ be a policy. Then the robust Bellman operator $T^{\pi,\mathcal U}$ has a unique fixed point $v^{\pi,\mathcal U}$, the **robust value function**, and $v^{\pi,\mathcal U}$ is the optimal solution of the robust optimization problem
--   $$\max_{v\in\mathbb R^{\mathcal S}}\ \langle v,\mu_0\rangle\quad\text{s.t.}\quad v\le T^\pi_{(P,r)}v\ \text{ for all }(P,r)\in\mathcal U. \tag{$P_{\mathcal U}$}$$
--
--   The result holds for general (not necessarily rectangular) uncertainty sets $\mathcal P\times\mathcal R$ and stochastic policies, and is the starting point of the equivalence between robustness and regularization: each later theorem rewrites the robust constraint of $(P_{\mathcal U})$ in closed form.
--
--   **Formalization Note.** The robust value function is encoded as the fixed point of $T^{\pi,\mathcal U}$, and its existence and uniqueness are part of the conclusion. The page defines $v^{\pi,\mathcal U}(s)$ as $\min_{(P,r)\in\mathcal U} v^\pi_{(P,r)}(s)$ and states it is this fixed point for rectangular sets (a cited fact); the paper's proof uses only the fixed-point property, which is also the meaningful object for non-rectangular $\mathcal U$. "The optimal solution" means feasible, objective-maximal, and the unique maximizer. The product form $\mathcal U = \mathcal P\times\mathcal R$ and the kernel property $\mathcal P\subseteq\Delta_{\mathcal S}^{\mathcal X}$ are the robust-MDP definition of p. 4; nonemptiness and compactness of $\mathcal P$ and $\mathcal R$ are made explicit so that the minimum is attained. For a non-rectangular $\mathcal U$ the pointwise minimum of p. 4 is in general strictly larger than this fixed point, and only the fixed point solves $(P_{\mathcal U})$; the page asserts the two coincide.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 5, Proposition 3.1 (proof in App. A.1, p. 15)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- Proposition 3.1 (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 5). For a robust MDP with
uncertainty set `U := 𝒫 × ℛ` (p. 4), `𝒫` a nonempty compact set of transition kernels and `ℛ` a
nonempty compact set of rewards (not necessarily rectangular), and any policy `π`, the robust
operator `T^{π,U}` has a unique fixed point `v^{π,U}` (the robust value function), and it is the
optimal solution of `(P_U)`: `max ⟨v, μ₀⟩ s.t. v ≤ T^π_{(P,r)} v for all (P, r) ∈ U`. -/
theorem proposition_3_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (Pset : Set (S → A → S → ℝ)) (hPne : Pset.Nonempty) (hPc : IsCompact Pset)
    (hPker : ∀ P ∈ Pset, FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (Rset : Set (S → A → ℝ)) (hRne : Rset.Nonempty) (hRc : IsCompact Rset)
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v →
      IsOptimalSolution μ₀ {w : S → ℝ | ∀ m ∈ Pset ×ˢ Rset, w ≤ evalOp γ m.1 m.2 π w} v := by sorry

end TwiceRegMDP.RobustReg
