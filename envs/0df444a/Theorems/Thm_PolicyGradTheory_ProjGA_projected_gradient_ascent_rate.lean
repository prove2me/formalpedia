-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_projected_gradient_ascent_rate
-- name    : PolicyGradTheory.ProjGA.projected_gradient_ascent_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:45:27.923737+00:00
-- url     : https://prove2.me/theorems/8acfccf3-b9b0-46ac-985e-e95b5cbc9354
-- title:
--   Theorem 4.1, p. 15 — projected gradient ascent with η = (1−γ)³/(2γ|A|): V⋆(ρ) − V^{(t)}(ρ) ≤ ε for some t ≤ T whenever T > 64γ|S||A|D²/((1−γ)⁶ε²)
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards $r(s,a)\in[0,1]$ and discount factor $\gamma\in(0,1)$. Let $\mu,\rho\in\Delta(\mathcal S)$ be state distributions, $\pi^\star$ an optimal policy with $V^\star=V^{\pi^\star}$, and $d^{\pi^\star}_\rho$ its discounted state visitation distribution from $\rho$. Let $D$ be a bound on the distribution mismatch coefficient, i.e. $d^{\pi^\star}_\rho(s)\le D\,\mu(s)$ for all $s$ (the smallest such $D$ is $\|d^{\pi^\star}_\rho/\mu\|_\infty$).
--
--   Run projected gradient ascent (9) on $V^\pi(\mu)$ under the direct parameterization,
--   $$
--   \pi^{(t+1)}=P_{\Delta(\mathcal A)^{|\mathcal S|}}\big(\pi^{(t)}+\eta\nabla_\pi V^{(t)}(\mu)\big),\qquad \eta=\frac{(1-\gamma)^3}{2\gamma|\mathcal A|},
--   $$
--   from any initial policy $\pi^{(0)}$, where $P_{\Delta(\mathcal A)^{|\mathcal S|}}$ is the Euclidean projection onto the product simplex.
--
--   **Theorem.** For every $\epsilon>0$ and every integer $T$ with
--   $$
--   T>\frac{64\gamma|\mathcal S||\mathcal A|}{(1-\gamma)^6\epsilon^2}\,D^2,
--   $$
--   there is an index $t\in\{0,1,\dots,T\}$ with $V^\star(\rho)-V^{(t)}(\rho)\le\epsilon$.
--
--   The guarantee holds simultaneously for all performance distributions $\rho$, although the algorithm only optimizes $V^\pi(\mu)$; the price of the mismatch between $\rho$ and $\mu$ is the factor $D^2$. It is the paper's first global convergence rate for a policy gradient method on a non-concave objective.
--
--   **Formalization Note** (1) The page states $\min_{t<T}$; its proof (p. 50) bounds $\min_{t=0,\dots,T}$ because Proposition B.1 transfers a small gradient mapping at $\pi^{(t)}$ to near-stationarity at $\pi^{(t+1)}$. The printed index range fails at $T=1$ (one state, two actions with rewards 1 and 0, $\gamma=0.001$, $\mu=\rho=\delta_s$, $D=1$, $\epsilon=1/2$, $\pi^{(0)}$ on the bad action), so the statement uses $t\le T$. (2) $\gamma>0$ is assumed: the step size divides by $\gamma$. (3) $\epsilon>0$ is assumed: the threshold divides by $\epsilon$. (4) The mismatch coefficient is any upper bound $D$, avoiding Lean's $x/0=0$. (5) The gradient is the Euclidean gradient of $\pi\mapsto V^\pi(\mu)$ on `EuclideanSpace ℝ (S × A)`, and the projection is any map satisfying the projection predicate.
-- source:
--   arXiv:1908.00261v5, Theorem 4.1, p. 15 (proof App. B.1, pp. 49–50)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Theorem 4.1, arXiv:1908.00261v5, p. 15: projected gradient ascent (9) on `V^π(μ)` with step
size `η = (1−γ)³/(2γ|A|)`, from any initial policy, satisfies, for every distribution `ρ`,
`V⋆(ρ) − V^{(t)}(ρ) ≤ ε` for some `t ≤ T` whenever `T > 64γ|S||A|/((1−γ)⁶ε²) · D²`, where `D` is
any bound `d^{π⋆}_ρ ≤ D μ` on the distribution mismatch coefficient `‖d^{π⋆}_ρ/μ‖_∞`. The index
range `t ≤ T` is the one the proof (p. 50) establishes; the printed `t < T` fails at `T = 1`. -/
theorem projected_gradient_ascent_rate {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (hγ : 0 < γ) (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj)
    (π : ℕ → EuclideanSpace ℝ (S × A)) (hπ0 : π 0 ∈ simplexSet S A)
    (hrun : IsProjGARun P r γ μ ((1 - γ) ^ 3 / (2 * γ * (Fintype.card A : ℝ))) Proj π)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ T : ℕ,
      64 * γ * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2 <
          (T : ℝ) →
        ∃ t ≤ T, valueAt πstar P r γ ρ - valueAt (asPolicy (π t)) P r γ ρ ≤ ε := by sorry

end PolicyGradTheory.ProjGA
