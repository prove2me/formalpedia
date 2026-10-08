-- Prove2me | Theorems.Thm_PGLandscape_Regularized_regularization_gap
-- name    : PGLandscape.Regularized.regularization_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:45.281158+00:00
-- url     : https://prove2.me/theorems/a771c594-bca5-490a-b875-87d1d42936d7
-- title:
--   Lemma 10, p. 20 — a minimizer π*_λ of ℓ_λ satisfies ℓ_0(π*_λ) ≤ min_π ℓ_0(π) + λ(1 + log(1 + c/λ)), c = 2 max|g_{s,i}|/(1−γ)
-- statement:
--   **Impact of regularization.** Consider the regularized finite MDP of Example 4: finitely many states, actions in the simplex $\Delta_{k-1}$, nonnegative cost vectors $g_s\in\mathbb R^k_+$, transitions $P(s'|s,a)=\sum_iP(s'|s,e_i)a_i$, discount factor $\gamma\in(0,1)$, initial distribution $\rho$, and regularized costs $g_\lambda(s,a)=g_s^\top a+\lambda D_{\mathrm{KL}}(U\|a)$ with $\lambda\ge0$. Let $\ell_\lambda$ be the regularized and $\ell_0$ the unregularized discounted average cost, and let
--
--   $$
--   c=\frac{2\,\max_{s,i}|g_{s,i}|}{1-\gamma}.
--   $$
--
--   If $\pi^*_\lambda\in\arg\min_{\pi\in\Pi}\ell_\lambda(\pi)$, then
--
--   $$
--   \ell_0(\pi^*_\lambda)\le\min_{\pi\in\Pi}\ell_0(\pi)+\lambda\Big(1+\log\Big(1+\frac c\lambda\Big)\Big).
--   $$
--
--   So an optimal policy of the relative-entropy (log-barrier) regularized problem is near-optimal for the unregularized one, with a gap of order $\lambda\log(1/\lambda)$ as $\lambda\downarrow0$.
--
--   **Formalization Note** The page prints the right-hand side as $\min_{\pi}\ell_\lambda(\pi)+\lambda(1+\log(1+c/\lambda))$. Because $D_{\mathrm{KL}}\ge0$, $\ell_0(\pi^*_\lambda)\le\ell_\lambda(\pi^*_\lambda)=\min_\pi\ell_\lambda(\pi)$, so the printed inequality holds trivially; the proof (p. 45) ends with $\min_\pi\ell_\lambda(\pi)\le\ell_\lambda(\pi_\lambda)\le\min_\pi\ell_0(\pi)+\lambda+\lambda\log(1+c/\lambda)$ and the text on p. 20 states the near-optimality for the un-regularized objective, which is the statement formalized here. At $\lambda=0$ Lean's convention $c/0=0$ makes the bound $0$, the limit of the page's bound as $\lambda\downarrow0$, and the statement says that a minimizer of $\ell_0$ minimizes $\ell_0$. $\ell_\lambda$ takes values in $[0,\infty]$ (it is $+\infty$ at policies with a zero action probability at a state of positive occupancy), and $\min_\pi\ell_0(\pi)$ is written as "$\le\ell_0(\pi)+\dots$ for every policy $\pi$". $\mathcal S$ and the action set are assumed nonempty, as they are on the page.
-- source:
--   arXiv:1906.01786v3, Lemma 10, p. 20 (restated p. 43); right-hand side as established at the end of the proof, p. 45

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PGLandscape_Regularized_Model
open FoundationsML.ReinforcementLearning
open scoped ENNReal

namespace PGLandscape.Regularized

/-- Lemma 10, p. 20 (restated p. 43), with the right-hand side the proof establishes (p. 45):
if `π*_λ ∈ argmin_{π∈Π} ℓ_λ(π)` with `λ ≥ 0`, then
`ℓ_0(π*_λ) ≤ min_{π∈Π} ℓ_0(π) + λ (1 + log(1 + c/λ))`, `c = 2 (max_{s,i} |g_{s,i}|)/(1 − γ)`. -/
theorem regularization_gap {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    [Nonempty S] [Nonempty I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (hlam : 0 ≤ lam)
    (πlam : S → I → ℝ) (hπlam : IsPolicy πlam)
    (hmin : ∀ π : S → I → ℝ, IsPolicy π → regLoss P gs γ ρ lam πlam ≤ regLoss P gs γ ρ lam π) :
    ∀ π : S → I → ℝ, IsPolicy π →
      loss0 P gs γ ρ πlam ≤ loss0 P gs γ ρ π + lam * (1 + Real.log (1 + costConst gs γ / lam)) := by sorry

end PGLandscape.Regularized
