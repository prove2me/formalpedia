-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_display12_var_sandwich
-- name    : TailRiskSharing.VaRConv.display12_var_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:24.107711+00:00
-- url     : https://prove2.me/theorems/33ad433f-9cb5-48cc-8c18-bbc6bb117279
-- title:
--   (12), p. 9 — VaR^L_{α₁−δ} ≥ VaR^R_{α₁} ≥ VaR^L_{α₁} for δ ∈ (0, α₁)
-- statement:
--   Let $\mathbb P$ be a probability measure, $\alpha_1\in(0,1)$ and $\delta\in(0,\alpha_1)$. For every random variable $X$,
--
--   $$\mathrm{VaR}^L_{\alpha_1-\delta}(X)\ \ge\ \mathrm{VaR}^R_{\alpha_1}(X)\ \ge\ \mathrm{VaR}^L_{\alpha_1}(X).$$
--
--   The right VaR at level $\alpha_1$ is squeezed between left VaRs; letting $\delta\downarrow0$ is how the proof of Theorem 1 passes from statements about left VaRs to right VaRs.
--
--   **Formalization Note** $X$ is measurable. Atomlessness is not assumed.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 9, proof of Theorem 1, display (12)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem display12_var_sandwich {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α₁ : ℝ) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < α₁)
    (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    VaRR P α₁ X ≤ VaRL P (α₁ - δ) X ∧ VaRL P α₁ X ≤ VaRR P α₁ X := by sorry

end TailRiskSharing.VaRConv
