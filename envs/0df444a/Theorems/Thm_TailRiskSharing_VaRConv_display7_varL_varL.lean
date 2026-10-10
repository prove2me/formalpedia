-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_display7_varL_varL
-- name    : TailRiskSharing.VaRConv.display7_varL_varL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:19.597049+00:00
-- url     : https://prove2.me/theorems/a93e75b9-6625-486f-a289-e4bd02d1c9ed
-- title:
--   (7), p. 9 — VaR^L_{α₁} □ VaR^L_{α₂} = VaR^L_{α₁+α₂} (Embrechts et al. 2018, Cor. 2)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, and let $\alpha_1,\alpha_2>0$ with $\alpha_1+\alpha_2<1$. For every random variable $X$,
--
--   $$\mathrm{VaR}^L_{\alpha_1}\,\square\,\mathrm{VaR}^L_{\alpha_2}(X)=\mathrm{VaR}^L_{\alpha_1+\alpha_2}(X).$$
--
--   In words: when two agents both measure risk by a left quantile, the smallest total capital achievable by splitting $X$ is the left quantile of $X$ at the summed level. The paper quotes it from Embrechts, Liu and Wang (2018), Corollary 2, and builds the mixed cases of Theorem 1 on it.
--
--   **Formalization Note** The domain is $L^0$ and the inf-convolution is computed in $[-\infty,\infty]$; the statement asserts that it equals the real number on the right.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 9, display (7) (= Embrechts, Liu & Wang 2018, Corollary 2)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem display7_varL_varL {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα : α₁ + α₂ < 1)
    (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    infConv L0 ![VaRL P α₁, VaRL P α₂] X = ((VaRL P (α₁ + α₂) X : ℝ) : EReal) := by sorry

end TailRiskSharing.VaRConv
