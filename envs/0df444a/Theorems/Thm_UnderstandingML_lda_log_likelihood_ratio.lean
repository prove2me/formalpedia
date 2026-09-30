-- Prove2me | Theorems.Thm_UnderstandingML_lda_log_likelihood_ratio
-- name    : UnderstandingML.lda_log_likelihood_ratio
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:34:24.734934+00:00
-- url     : https://prove2.me/theorems/a0e8abdd-47d6-46f7-a561-eb96c072354e
-- title:
--   Equation (24.8): the LDA log-likelihood ratio ½(x−μ₀)ᵀΣ⁻¹(x−μ₀) − ½(x−μ₁)ᵀΣ⁻¹(x−μ₁) equals ⟨w, x⟩ + b with w = Σ⁻¹(μ₁−μ₀), b = ½(μ₀ᵀΣ⁻¹μ₀ − μ₁ᵀΣ⁻¹μ₁)
-- statement:
--   **Equation (24.8).** In the LDA setting the log-likelihood ratio becomes $\frac12(x-\mu_0)^\top\Sigma^{-1}(x-\mu_0) - \frac12(x-\mu_1)^\top\Sigma^{-1}(x-\mu_1)$, which can be rewritten as $\langle w, x\rangle + b$ where $w = (\mu_1 - \mu_0)^\top\Sigma^{-1}$ and $b = \frac12(\mu_0^\top\Sigma^{-1}\mu_0 - \mu_1^\top\Sigma^{-1}\mu_1)$. As a result, under the generative assumptions of LDA the Bayes optimal classifier is a linear classifier.
--
--   Formally: the identity for any symmetric matrix $M$ in the role of $\Sigma^{-1}$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.3 p. 348, Equation (24.8)

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Equation (24.8)** (p. 348). Under the LDA assumptions the log-likelihood ratio
`½(x − μ₀)ᵀΣ⁻¹(x − μ₀) − ½(x − μ₁)ᵀΣ⁻¹(x − μ₁)` equals `⟨w, x⟩ + b` with `w = Σ⁻¹(μ₁ − μ₀)` and
`b = ½(μ₀ᵀΣ⁻¹μ₀ − μ₁ᵀΣ⁻¹μ₁)`, so the Bayes optimal classifier is linear. Stated for any symmetric
matrix `M` in the role of `Σ⁻¹`. -/
theorem lda_log_likelihood_ratio {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm)
    (μ₀ μ₁ x : Fin d → ℝ) :
    1 / 2 * dotProduct (x - μ₀) (M.mulVec (x - μ₀)) - 1 / 2 * dotProduct (x - μ₁) (M.mulVec (x - μ₁)) =
      dotProduct (M.mulVec (μ₁ - μ₀)) x +
        1 / 2 * (dotProduct μ₀ (M.mulVec μ₀) - dotProduct μ₁ (M.mulVec μ₁)) := by sorry

end UnderstandingML
