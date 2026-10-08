-- Prove2me | Theorems.Thm_PGLandscape_Concentrability_conc_le_density_bound
-- name    : PGLandscape.Concentrability.conc_le_density_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:36.136174+00:00
-- url     : https://prove2.me/theorems/2bcfddde-2435-4fd3-99bb-c630aab5846f
-- title:
--   Theorem 4(b), pp. 24–25 — κ_ρ ≤ ‖dη_{π*}/dρ‖_∞: every C with η_{π*} ≤ Cρ satisfies the concentrability bound (13)
-- statement:
--   Throughout, $(\mathcal S,(\mathcal A_s)_{s\in\mathcal S},g,P,\gamma,\rho)$ is the discounted Markov decision process of §2 of the paper: states in a measurable space $\mathcal S$, feasible action sets $\mathcal A_s$, a bounded measurable per-period cost $g$, a transition kernel $P(\cdot\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. For a measurable stationary policy $\pi$, $J_\pi$ is its cost-to-go, $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure and $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ its discounted average cost. $T_\pi J(s)=g(s,\pi(s))+\gamma\int J(s')P(ds'\mid s,\pi(s))$ and $TJ(s)=\min_{a\in\mathcal A_s}[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)]$ are the Bellman operators, $\Pi$ is the set of feasible measurable stationary policies, $\pi^*\in\Pi$ is an optimal policy and $J^*=J_{\pi^*}$. The policy class is $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ for a convex $\Theta\subseteq\mathbb R^d$ with every $\pi_\theta$ feasible; the result holds for every such class.
--
--   The effective concentrability coefficient $\kappa_\rho$ (Definition 3, p. 16) is the smallest scalar $\kappa$ with $\|J-J^*\|_{1,\rho}\le\frac{\kappa}{1-\gamma}\|J-TJ\|_{1,\rho}$ for all $J\in\mathcal J_\Theta=\{J_{\pi_\theta}:\theta\in\Theta\}$, (13). Since the right-hand side is nondecreasing in $\kappa$, the claim $\kappa_\rho\le X$ is exactly the claim that $X$ satisfies (13); this is how it is stated in Lean (`IsConcBound`).
--
--   **Theorem 4(b).** Let $\pi^*$ be any optimal stationary policy, and let $C$ be a real number such that
--   $$\eta_{\pi^*}(B)\le C\,\rho(B)\qquad\text{for every measurable }B\subseteq\mathcal S.$$
--   Then $\kappa_\rho\le C$, that is,
--   $$\|J-J^*\|_{1,\rho}\le\frac{C}{1-\gamma}\,\|J-TJ\|_{1,\rho}\qquad\forall J\in\mathcal J_\Theta .$$
--   Equivalently, $\kappa_\rho\le\big\|\tfrac{d\eta_{\pi^*}}{d\rho}\big\|_\infty$.
--
--   The bound converts the weighted Bellman error of any policy in the class into its optimality gap, at the price of the worst-case likelihood ratio between the optimal occupancy measure and the initial distribution. It is the main sufficient condition under which the gradient-dominance and convergence-rate results of the paper (Theorem 2, Theorem 5) are non-vacuous.
--
--   **Formalization Note** For $C\ge0$, $\|d\eta_{\pi^*}/d\rho\|_\infty\le C$ holds if and only if $\eta_{\pi^*}(B)\le C\rho(B)$ for every measurable $B$ (the paper notes this on p. 25), so quantifying over all such $C$ is the paper's statement; it avoids a real-valued essential supremum, which would read $0$ exactly when the paper's bound is $+\infty$. The hypothesis forces $C\ge1$ (take $B=\mathcal S$). Assumption 1 ($\eta_{\pi^*}\ll\rho$) and Assumption 2 (measurable selection: for every bounded measurable $J$ some $\pi\in\Pi$ attains the minimum in $TJ$ at every state) are standing assumptions of the paper and are hypotheses here. States and actions are arbitrary measurable spaces (the paper's Borel subsets of $\mathbb R^n$, $\mathbb R^k$ are a special case; no argument uses the Euclidean structure), and $g$, $P$ are given on all of $\mathcal S\times\mathcal A$; only their values on feasible pairs matter. The optimal policy is a binder $\pi^*$ with `IsOptimal`, so $J^*=J_{\pi^*}$. The paper prints $T_\pi$ and $T$ in (3)–(4) without the factor $\gamma$; every later use (Assumption 2, (6), (7), the proofs) has it, and the formalization includes it.
-- source:
--   arXiv:1906.01786v3, Theorem 4(b), pp. 24–25 (restated p. 42; proof p. 42); Definition 3, (13), p. 16

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.Concentrability

open MeasureTheory ProbabilityTheory

/-- Theorem 4(b), pp. 24–25 (restated p. 42): `κ_ρ ≤ ‖dη_{π*}/dρ‖_∞`, in the form: every `C` with
`η_{π*}(B) ≤ C ρ(B)` for all measurable `B` satisfies (13). -/
theorem conc_le_density_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA1 : PGLandscape.Closure.Assumption1 M πstar)
    (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A)
    (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (C : ℝ) (hC : ∀ B, MeasurableSet B → PGLandscape.Closure.occupancy M πstar B ≤ ENNReal.ofReal C * M.ρ B) :
    PGLandscape.Closure.IsConcBound M Θ πθ πstar C := by sorry

end PGLandscape.Concentrability
