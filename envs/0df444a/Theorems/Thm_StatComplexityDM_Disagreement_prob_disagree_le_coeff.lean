-- Prove2me | Theorems.Thm_StatComplexityDM_Disagreement_prob_disagree_le_coeff
-- name    : StatComplexityDM.Disagreement.prob_disagree_le_coeff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:19.29275+00:00
-- url     : https://prove2.me/theorems/7c05f105-ba10-4620-bab2-a4600bce8d9d
-- title:
--   Lemma E.2 (proof), p. 105 — P(∃f ∈ F : |f(π)| > δ, E[f²] ≤ ϵ²) ≤ (ϵ²/δ²)·θ(F, Δ, ε; ρ) for ϵ ≥ ε, δ ≥ Δ
-- statement:
--   Let $\mathcal{F}$ be a class of functions $\Pi \to [-R, R]$, let $\rho$ be a finitely supported distribution on $\Pi$, and let $\Delta_0 > 0$, $\varepsilon_0 > 0$. Then for all $\delta \ge \Delta_0$ and $\epsilon \ge \varepsilon_0$,
--   $$
--   \mathbb{P}_{\pi\sim\rho}\bigl( \exists f \in \mathcal{F} : |f(\pi)| > \delta,\ \mathbb{E}_{\pi'\sim\rho}[f^2(\pi')] \le \epsilon^2 \bigr) \le \frac{\epsilon^2}{\delta^2}\, \theta(\mathcal{F}, \Delta_0, \varepsilon_0; \rho),
--   $$
--   where $\theta$ is the disagreement coefficient of Definition 6.3 and $\pi' \sim \rho$ is independent of $\pi$.
--
--   This is the step of the proof of Lemma E.2 at which the disagreement coefficient enters: it converts the probability of disagreement at every pair of scales into $\theta$.
--
--   **Formalization Note** The page states the step for the class with $R = 1$ and $\Delta, \varepsilon \in (0, 1]$; the statement here holds for any uniform bound $R$ and any positive $\Delta_0, \varepsilon_0$, which contains the page's case. The bound $R$ makes the supremum in $\theta$ finite. Distributions are finitely supported.
-- source:
--   arXiv:2112.13487v3, App. E.2.1, proof of Lemma E.2, p. 105 ("Now, from the definition of the disagreement coefficient")

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

namespace StatComplexityDM.Disagreement

/-- Proof of Lemma E.2, p. 105 (arXiv:2112.13487v3): from the definition of the disagreement
coefficient, for a class `F` of functions bounded by `R` in absolute value, a finitely supported
`ρ`, `Δ₀ > 0`, `ε₀ > 0`, and all `ε ≥ ε₀`, `δ ≥ Δ₀`,
`P_{π∼ρ}(∃ f ∈ F : |f(π)| > δ ∧ E_{π′∼ρ}[f²(π′)] ≤ ε²) ≤ (ε²/δ²) · θ(F, Δ₀, ε₀; ρ)`. -/
theorem prob_disagree_le_coeff {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (R : ℝ)
    (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (ρw : κ → ℝ) (ρpt : κ → Act) (hρ : StatComplexityDM.LowerBound.IsDist ρw)
    (Δ₀ ε₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hε₀ : 0 < ε₀) (δ ε : ℝ) (hδ : Δ₀ ≤ δ) (hε : ε₀ ≤ ε) :
    distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt)
      ≤ ε ^ 2 / δ ^ 2 * disagreementCoeff F Δ₀ ε₀ ρw ρpt := by sorry

end StatComplexityDM.Disagreement
