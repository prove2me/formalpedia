-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_log_barrier_iteration_complexity
-- name    : PolicyGradTheory.LogBarrier.log_barrier_iteration_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:59:02.927983+00:00
-- url     : https://prove2.me/theorems/a94f2d3c-264b-45e7-a668-6c15fd12643f
-- title:
--   Corollary 5.1, p. 21 — log-barrier softmax PG with λ = ε(1−γ)/(2D), η = 1/β_λ: min_{t<T} V⋆(ρ) − V⁽ᵗ⁾(ρ) ≤ ε once T ≥ 320|S|²|A|²D²/((1−γ)⁶ε²)
-- statement:
--   Let $(P,r,\gamma)$ be a finite MDP with nonempty action set, rewards in $[0,1]$ and $\gamma\in[0,1)$; let $\pi^\star$ be an optimal policy and $V^\star=V^{\pi^\star}$. Let $\mu,\rho\in\Delta(\mathcal S)$ and let $D$ satisfy $d^{\pi^\star}_\rho(s)\le D\,\mu(s)$ for every state $s$ (for instance $D=\|d^{\pi^\star}_\rho/\mu\|_\infty$). Fix $\epsilon>0$ and set
--   $$
--   \lambda=\frac{\epsilon(1-\gamma)}{2D},\qquad\beta_\lambda=\frac{8}{(1-\gamma)^3}+\frac{2\lambda}{|\mathcal S|},\qquad\eta=\frac1{\beta_\lambda}.
--   $$
--   Let $(\theta^{(t)})_{t\ge0}$ be the gradient ascent run (13) on the log barrier regularized objective $L_\lambda$ (12) with step size $\eta$, started from a parameter $\theta^{(0)}$ whose softmax policy is uniform at every state ($\theta^{(0)}_{s,a}$ independent of $a$, e.g. $\theta^{(0)}=0$). Write $V^{(t)}=V^{\pi_{\theta^{(t)}}}$. Then
--   $$
--   \min_{t<T}\big\{V^\star(\rho)-V^{(t)}(\rho)\big\}\le\epsilon\quad\text{whenever}\quad T\ge\frac{320\,|\mathcal S|^2|\mathcal A|^2}{(1-\gamma)^6\,\epsilon^2}\,D^2 .
--   $$
--
--   This is the polynomial iteration complexity of softmax policy gradient with log barrier regularization, the Table 1 entry for this method: the number of steps is polynomial in $|\mathcal S|$, $|\mathcal A|$, $1/(1-\gamma)$, $1/\epsilon$ and the distribution mismatch coefficient.
--
--   **Formalization Note.** Two hypotheses differ from the printed corollary, both following the proof in Appendix C.2 (p. 69). (1) The printed text starts "from any initial $\theta^{(0)}$", but the proof bounds $L_\lambda(\theta^\star)-L_\lambda(\theta^{(0)})\le 1/(1-\gamma)$, which holds when $\pi^{(0)}$ is uniform (the KL term vanishes) and fails for arbitrary $\theta^{(0)}$: starting far from uniform, the iteration needs more steps than any bound independent of $\theta^{(0)}$. The uniform start is assumed. (2) The printed $\beta_\lambda=8\gamma/(1-\gamma)^3+2\lambda/|\mathcal S|$ contradicts the proof's "By Lemma D.4, we can take $\beta_\lambda$", and Lemma D.4 proves $8/(1-\gamma)^3+2\lambda/|\mathcal S|$; the latter is used, and the iteration count is unchanged because the proof's estimate already uses $8$. The mismatch coefficient is encoded by any upper bound $D$ (no division by $\mu(s)$), and the same $D$ sets $\lambda$; the page's choice is the instance $D=\|d^{\pi^\star}_\rho/\mu\|_\infty$. The minimum over $t<T$ is written as the existence of some $t<T$.
-- source:
--   arXiv:1908.00261v5, Corollary 5.1, p. 21; proof in App. C.2, pp. 68–69, (48)–(49)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- Corollary 5.1 (iteration complexity with log barrier regularization),
arXiv:1908.00261v5, p. 21, with two disclosed corrections of the printed statement (taken from
its proof, p. 69): the run starts from a parameter whose policy is uniform at every state
(`θ^{(0)}_{s,·}` constant, e.g. `θ^{(0)} = 0`), and `β_λ = 8/(1−γ)³ + 2λ/|S|` is the constant of
Lemma D.4. With `λ = ε(1−γ)/(2D)` and `η = 1/β_λ`, `min_{t<T} {V⋆(ρ) − V^{(t)}(ρ)} ≤ ε` whenever
`T ≥ 320|S|²|A|²D²/((1−γ)⁶ε²)`, for any `D` with `d^{π⋆}_ρ ≤ D µ`. -/
theorem log_barrier_iteration_complexity {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ) (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (D : ℝ) (hD : ∀ s, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s ≤ D * μ s)
    (ε : ℝ) (hε : 0 < ε) (lam : ℝ) (hlam : lam = ε * (1 - γ) / (2 * D))
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hθ0 : ∀ s a a', θ 0 (s, a) = θ 0 (s, a'))
    (hrun : IsLogBarrierRun P r γ μ lam (1 / betaLam S γ lam) θ) :
    ∀ T : ℕ,
      320 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) ^ 2 / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2
          ≤ (T : ℝ) →
        ∃ t < T, PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ - PolicyGradTheory.ProjGA.valueAt (PolicyGradTheory.Softmax.softmaxPolicy (θ t)) P r γ ρ ≤ ε := by sorry

end PolicyGradTheory.LogBarrier
