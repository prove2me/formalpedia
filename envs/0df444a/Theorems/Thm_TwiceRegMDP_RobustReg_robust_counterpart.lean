-- Prove2me | Theorems.Thm_TwiceRegMDP_RobustReg_robust_counterpart
-- name    : TwiceRegMDP.RobustReg.robust_counterpart
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:46:28.952994+00:00
-- url     : https://prove2.me/theorems/a889f8b5-aeda-44e9-a61c-51956fd92ed8
-- title:
--   Proof of Theorem 4.1 (App. B.1) — closed form of the robust counterpart $F(s)$
-- statement:
--   Let $P_0$ be a transition array, $r_0\in\mathbb R^{\mathcal X}$ a reward, $\gamma\in\mathbb R$, and for every state $s$ let $\mathcal P_s\subseteq\mathbb R^{\mathcal X}$ and $\mathcal R_s\subseteq\mathbb R^{\mathcal A}$ be nonempty and compact. Let $\mathcal U = (P_0+\mathcal P)\times(r_0+\mathcal R)$ be the s-rectangular uncertainty set. Fix a policy-like array $\pi$, a vector $v\in\mathbb R^{\mathcal S}$ and a state $s$, and define the robust counterpart
--   $$F(s) := \max_{(P,r)\in\mathcal U}\big\{v(s)-r^\pi(s)-\gamma P^\pi v(s)\big\}.$$
--   Then the maximum is attained and
--   $$F(s) = \sigma_{\mathcal P_s}(-\gamma v\cdot\pi_s)+\sigma_{\mathcal R_s}(-\pi_s)+v(s)-T^\pi_{(P_0,r_0)}v(s),$$
--   where $[v\cdot\pi_s](s',a) = v(s')\pi_s(a)$.
--
--   This identity converts the robust constraint "$F(s)\le 0$ for all $s$" of the robust program into the regularized constraint of Theorem 4.1, and is the computational core of its proof.
--
--   **Formalization Note.** The statement asserts that the closed-form value is the greatest element of the set of values $\{v(s)-r^\pi(s)-\gamma P^\pi v(s) : (P,r)\in\mathcal U\}$, i.e. that the maximum exists and equals it. It needs no kernel or policy hypothesis, which the identity does not use.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, proof of Theorem 4.1, App. B.1, pp. 20–21 (definition of F(s) on p. 20; closed form on p. 21)

import Mathlib
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- The robust counterpart in closed form (Derman–Geist–Mannor, arXiv:2110.06267v1, proof of
Theorem 4.1, App. B.1, pp. 20–21). For `U = (P₀ + 𝒫) × (r₀ + ℛ)` with every `𝒫_s` and `ℛ_s`
nonempty and compact, every `v` and every state `s`,
`F(s) := max_{(P,r) ∈ U} {v(s) − r^π(s) − γ P^π v(s)}` equals
`σ_{𝒫_s}(−γ v · π_s) + σ_{ℛ_s}(−π_s) + v(s) − T^π_{(P₀,r₀)} v(s)`. -/
theorem robust_counterpart {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (Pset : S → Set (S × A → ℝ)) (hPne : ∀ s, (Pset s).Nonempty) (hPc : ∀ s, IsCompact (Pset s))
    (Rset : S → Set (A → ℝ)) (hRne : ∀ s, (Rset s).Nonempty) (hRc : ∀ s, IsCompact (Rset s))
    (π : S → A → ℝ) (v : S → ℝ) (s : S) :
    IsGreatest
      ((fun m : (S → A → S → ℝ) × (S → A → ℝ) =>
          v s - rewardPi π m.2 s - γ * transPi π m.1 v s) '' rectUncertainty P₀ r₀ Pset Rset)
      (supportFn (Pset s) (-(γ • vDotPi v π s)) + supportFn (Rset s) (-(π s))
        + v s - evalOp γ P₀ r₀ π v s) := by sorry

end TwiceRegMDP.RobustReg
