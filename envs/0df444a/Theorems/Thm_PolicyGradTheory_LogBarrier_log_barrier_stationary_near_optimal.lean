-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_log_barrier_stationary_near_optimal
-- name    : PolicyGradTheory.LogBarrier.log_barrier_stationary_near_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:40.769198+00:00
-- url     : https://prove2.me/theorems/a50a9c68-bf7b-406c-872d-012332996c0a
-- title:
--   Theorem 5.2, p. 20 — ε_opt-stationary points of L_λ with ε_opt ≤ λ/(2|S||A|) satisfy V^{π_θ}(ρ) ≥ V⋆(ρ) − (2λ/(1−γ))‖d^{π⋆}_ρ/µ‖∞
-- statement:
--   Let $(P,r,\gamma)$ be a finite MDP with an optimal policy $\pi^\star$ and $V^\star=V^{\pi^\star}$, let $\mu,\rho\in\Delta(\mathcal S)$, and let $\lambda>0$. Suppose $\theta$ is such that
--   $$
--   \|\nabla_\theta L_\lambda(\theta)\|_2\le\epsilon_{\mathrm{opt}}\quad\text{and}\quad\epsilon_{\mathrm{opt}}\le\frac{\lambda}{2|\mathcal S|\,|\mathcal A|},
--   $$
--   where $L_\lambda$ is the log barrier regularized objective (12). Then
--   $$
--   V^{\pi_\theta}(\rho)\ge V^\star(\rho)-\frac{2\lambda}{1-\gamma}\,D
--   $$
--   for every $D$ with $d^{\pi^\star}_\rho(s)\le D\,\mu(s)$ for all states $s$; in particular for $D=\|d^{\pi^\star}_\rho/\mu\|_\infty$, the distribution mismatch coefficient (Definition 3.1).
--
--   Approximately stationary points of the regularized objective are therefore approximately optimal for the unregularized one, with an error proportional to $\lambda$ and to the mismatch between $\mu$ and the optimal policy's visitation.
--
--   **Formalization Note.** The mismatch coefficient is encoded by an upper bound $D$, avoiding division by $\mu(s)=0$; when the coefficient is $+\infty$ no such $D$ exists and the statement is vacuous, as on the page. $\pi^\star$ is any policy that is optimal at every state (`IsOptimalPolicy`). $\lambda>0$ is implicit on the page and stated explicitly; the action set is nonempty.
-- source:
--   arXiv:1908.00261v5, Theorem 5.2, p. 20

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- Theorem 5.2 (log barrier regularization), arXiv:1908.00261v5, p. 20: if
`‖∇_θ L_λ(θ)‖₂ ≤ ε_opt` and `ε_opt ≤ λ/(2|S||A|)`, then for every start distribution `ρ`,
`V^{π_θ}(ρ) ≥ V⋆(ρ) − (2λ/(1−γ)) ‖d^{π⋆}_ρ/µ‖_∞`; the mismatch coefficient is replaced by any
`D` with `d^{π⋆}_ρ ≤ D µ` componentwise. -/
theorem log_barrier_stationary_near_optimal {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ) (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (D : ℝ) (hD : ∀ s, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s ≤ D * μ s)
    (lam : ℝ) (hlam : 0 < lam) (εopt : ℝ) (θ : EuclideanSpace ℝ (S × A))
    (hgrad : ‖gradient (logBarrierObj P r γ μ lam) θ‖ ≤ εopt)
    (hεopt : εopt ≤ lam / (2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ))) :
    PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ - 2 * lam / (1 - γ) * D ≤ PolicyGradTheory.ProjGA.valueAt (PolicyGradTheory.Softmax.softmaxPolicy θ) P r γ ρ := by sorry

end PolicyGradTheory.LogBarrier
