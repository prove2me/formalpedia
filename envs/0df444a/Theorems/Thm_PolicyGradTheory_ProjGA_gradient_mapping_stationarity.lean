-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_gradient_mapping_stationarity
-- name    : PolicyGradTheory.ProjGA.gradient_mapping_stationarity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:45:17.566611+00:00
-- url     : https://prove2.me/theorems/5b02f405-954d-4aad-839f-eeb22fb50562
-- title:
--   Proposition B.1, p. 49 — ‖G^η(π)‖₂ ≤ ε implies δᵀ∇_πV^{π⁺}(μ) ≤ ε(ηβ + 1) for feasible unit directions δ at π⁺
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$, and $\mu\in\Delta(\mathcal S)$. Under the direct parameterization, suppose $V^\pi(\mu)$ is $\beta$-smooth in $\pi$ on the policy simplex, $\beta\ge0$:
--   $\|\nabla_\pi V^\pi(\mu)-\nabla_\pi V^{\pi'}(\mu)\|_2\le\beta\|\pi-\pi'\|_2$ for all policies $\pi,\pi'$. For a step size $\eta>0$ define the gradient mapping
--   $$
--   G^\eta(\pi)=\frac1\eta\Big(P_{\Delta(\mathcal A)^{|\mathcal S|}}\big(\pi+\eta\nabla_\pi V^\pi(\mu)\big)-\pi\Big)
--   $$
--   and the projected gradient update $\pi^+=\pi+\eta G^\eta(\pi)$.
--
--   **Proposition.** Let $\pi$ be a policy. If $\|G^\eta(\pi)\|_2\le\epsilon$, then
--   $$
--   \delta^\top\nabla_\pi V^{\pi^+}(\mu)\le\epsilon(\eta\beta+1)
--   $$
--   for every $\delta$ with $\|\delta\|_2\le1$ and $\pi^++\delta\in\Delta(\mathcal A)^{|\mathcal S|}$.
--
--   In words: a small gradient mapping at $\pi$ makes the next iterate $\pi^+$ approximately first-order stationary. This converts the rate of Theorem E.1 for the gradient mapping into the stationarity that the gradient domination lemma needs.
--
--   **Formalization Note** The page writes the maximum over $\pi+\delta\in\Delta(\mathcal A)^{|\mathcal S|}$; the proof bounds $\delta^\top\nabla_\pi V^{\pi^+}(\mu)$ for $\delta$ in the tangent cone at $\pi^+$, and the proof of Theorem 4.1 uses the bound at $\pi^{(t+1)}$. The statement therefore takes the feasible directions at $\pi^+$. The page's standing assumptions $\eta>0$ and $\beta\ge0$ are explicit. The maximum is stated as a bound on every feasible $\delta$.
-- source:
--   arXiv:1908.00261v5, Proposition B.1, p. 49 (proof via Theorem E.2, p. 77)

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Proposition B.1, arXiv:1908.00261v5, p. 49: let `V^π(μ)` be `β`-smooth in `π` (on the
policies), `η > 0`, `G^η(π) = (1/η)(P_{∆(A)^{|S|}}(π + η∇_π V^π(μ)) − π)` and
`π⁺ = π + ηG^η(π)`. If `‖G^η(π)‖₂ ≤ ε`, then `δᵀ∇_π V^{π⁺}(μ) ≤ ε(ηβ + 1)` for every `δ` with
`‖δ‖₂ ≤ 1` and `π⁺ + δ ∈ ∆(A)^{|S|}` (feasible directions at `π⁺`, as in the proof). -/
theorem gradient_mapping_stationarity {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (β : ℝ) (hβ : 0 ≤ β)
    (hsmooth : ∀ π ∈ simplexSet S A, ∀ π' ∈ simplexSet S A,
      ‖gradient (directValue P r γ μ) π - gradient (directValue P r γ μ) π'‖ ≤ β * ‖π - π'‖)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj)
    (η : ℝ) (hη : 0 < η) (ε : ℝ) (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A)
    (hG : ‖(1 / η) • (Proj (π + η • gradient (directValue P r γ μ) π) - π)‖ ≤ ε) :
    ∀ δ : EuclideanSpace ℝ (S × A),
      Proj (π + η • gradient (directValue P r γ μ) π) + δ ∈ simplexSet S A → ‖δ‖ ≤ 1 →
        inner ℝ δ (gradient (directValue P r γ μ)
          (Proj (π + η • gradient (directValue P r γ μ) π))) ≤ ε * (η * β + 1) := by sorry

end PolicyGradTheory.ProjGA
