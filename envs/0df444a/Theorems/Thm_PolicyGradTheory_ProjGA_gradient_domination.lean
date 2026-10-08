-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_gradient_domination
-- name    : PolicyGradTheory.ProjGA.gradient_domination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:44:55.179983+00:00
-- url     : https://prove2.me/theorems/a3c2a7f5-803e-4c45-b92f-b5883c69db53
-- title:
--   Lemma 4.1, p. 14 — gradient domination: V⋆(ρ) − V^π(ρ) ≤ ‖d^{π⋆}_ρ/d^π_μ‖_∞ max_π̄ (π̄−π)ᵀ∇V ≤ (1/(1−γ))‖d^{π⋆}_ρ/μ‖_∞ max_π̄ (π̄−π)ᵀ∇V
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, let $\mu,\rho\in\Delta(\mathcal S)$ be state distributions, and let $\pi^\star$ be an optimal policy, with $V^\star=V^{\pi^\star}$. Use the direct parameterization, and write $\nabla_\pi V^\pi(\mu)$ for the gradient of $\pi\mapsto V^\pi(\mu)$.
--
--   **Lemma (gradient domination).** For every policy $\pi\in\Delta(\mathcal A)^{|\mathcal S|}$,
--   $$
--   V^\star(\rho)-V^\pi(\rho)\;\le\;\Big\|\frac{d^{\pi^\star}_\rho}{d^\pi_\mu}\Big\|_\infty\max_{\bar\pi}\,(\bar\pi-\pi)^\top\nabla_\pi V^\pi(\mu)\;\le\;\frac1{1-\gamma}\Big\|\frac{d^{\pi^\star}_\rho}{\mu}\Big\|_\infty\max_{\bar\pi}\,(\bar\pi-\pi)^\top\nabla_\pi V^\pi(\mu),
--   $$
--   where the maximum is over all policies $\bar\pi\in\Delta(\mathcal A)^{|\mathcal S|}$ and the ratios are componentwise.
--
--   The lemma says that a policy that is nearly first-order stationary for the objective $V^\pi(\mu)$ is nearly optimal for every start distribution $\rho$, provided $\mu$ covers the states visited by an optimal policy. It is the reason projected gradient ascent converges globally despite the non-concavity of $V^\pi$.
--
--   **Formalization Note** The maximum is represented by an arbitrary upper bound $G\ge(\bar\pi-\pi)^\top\nabla_\pi V^\pi(\mu)$ for all policies $\bar\pi$ (the maximum is attained on the compact simplex, so this is equivalent). The two mismatch coefficients are represented by arbitrary constants $D_1$, $D$ with $d^{\pi^\star}_\rho(s)\le D_1\,d^\pi_\mu(s)$ and $d^{\pi^\star}_\rho(s)\le D\,\mu(s)$ for all $s$, which avoids Lean's convention $x/0=0$. The conclusion is the two inequalities $V^\star(\rho)-V^\pi(\rho)\le D_1G$ and $V^\star(\rho)-V^\pi(\rho)\le\frac{1}{1-\gamma}DG$. Optimality of $\pi^\star$ means $V^{\pi'}(s)\le V^{\pi^\star}(s)$ for every policy $\pi'$ and state $s$.
-- source:
--   arXiv:1908.00261v5, Lemma 4.1, p. 14 (proof pp. 14–15)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Lemma 4.1 (gradient domination), arXiv:1908.00261v5, p. 14: for the direct parameterization,
all state distributions `μ, ρ` and every policy `π`,
`V⋆(ρ) − V^π(ρ) ≤ ‖d^{π⋆}_ρ/d^π_μ‖_∞ max_{π̄} (π̄ − π)ᵀ∇_π V^π(μ)
  ≤ (1/(1−γ)) ‖d^{π⋆}_ρ/μ‖_∞ max_{π̄} (π̄ − π)ᵀ∇_π V^π(μ)`, the max over all policies `π̄`.
The max is passed as any upper bound `G`, the two mismatch coefficients as any `D₁`, `D` with
`d^{π⋆}_ρ ≤ D₁ d^π_μ` and `d^{π⋆}_ρ ≤ D μ` componentwise. -/
theorem gradient_domination {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A)
    (G : ℝ) (hG : ∀ πbar ∈ simplexSet S A,
      inner ℝ (πbar - π) (gradient (directValue P r γ μ) π) ≤ G)
    (D₁ : ℝ) (hD₁ : ∀ s, visitation πstar P γ ρ s ≤ D₁ * visitation (asPolicy π) P γ μ s)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s) :
    valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ D₁ * G ∧
      valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ 1 / (1 - γ) * D * G := by sorry

end PolicyGradTheory.ProjGA
