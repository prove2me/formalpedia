-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_lemma_2_1
-- name    : SmoothCCP.PenaltyModel.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:26.012192+00:00
-- url     : https://prove2.me/theorems/9f648733-148f-456b-8079-28f169a1da63
-- title:
--   Lemma 2.1 — the smoothed quantile equation (2.3) has a unique solution when (1 − α)N ∉ ℤ
-- statement:
--   Let $\varepsilon>0$, let $\gamma_\varepsilon:[-\varepsilon,\varepsilon]\to[0,1]$ be strictly decreasing, and suppose the smoothed indicator $\Gamma_\varepsilon$ of (2.2) is differentiable on $\mathbb R$. Let $0<\alpha<1$, $N\ge1$, and suppose $(1-\alpha)N\notin\mathbb Z$. Then for every $z\in\mathbb R^N$ the equation
--   $$
--   \sum_{i=1}^N\Gamma_\varepsilon(z_i-q)=(1-\alpha)N \tag{2.3}
--   $$
--   has exactly one solution $q\in\mathbb R$. Moreover, this solution is the smoothed quantile $Q_\varepsilon(z)$, defined as the least $q$ with $\sum_i\Gamma_\varepsilon(z_i-q)\ge(1-\alpha)N$.
--
--   The lemma is what makes $Q_\varepsilon$ a well-defined function of the sample values, so that the approximation (2.4) and the penalty function (5.3) make sense.
--
--   **Formalization Note** The lemma does not assume symmetry of $\gamma_\varepsilon$ or the quartic kernel, and neither does this statement. The second conjunct ties the definition `smoothQuantile` (a least root) to the root of (2.3).
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Lemma 2.1, p. 7

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Lemma 2.1, arXiv:1905.07377v2, p. 7: for a strictly decreasing γ_ε : [−ε, ε] → [0, 1] making Γ_ε
differentiable and (1 − α)N ∉ ℤ, equation (2.3) has a unique solution, and the least root
`smoothQuantile ε γ α z` is that solution. -/
theorem lemma_2_1 {N : ℕ} (ε α : ℝ) (γ : ℝ → ℝ) (hε : 0 < ε)
    (hγmaps : ∀ y ∈ Set.Icc (-ε) ε, γ y ∈ Set.Icc (0 : ℝ) 1)
    (hγanti : StrictAntiOn γ (Set.Icc (-ε) ε))
    (hΓdiff : Differentiable ℝ (SmoothCCP.Feasibility.Gam ε γ))
    (hα0 : 0 < α) (hα1 : α < 1) (hN : 1 ≤ N) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k)
    (z : Fin N → ℝ) :
    (∃! q : ℝ, ∑ i, SmoothCCP.Feasibility.Gam ε γ (z i - q) = (1 - α) * N) ∧
      ∑ i, SmoothCCP.Feasibility.Gam ε γ (z i - smoothQuantile ε γ α z) = (1 - α) * N := by sorry

end SmoothCCP.PenaltyModel
