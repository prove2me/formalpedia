-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_display14_varR_varL
-- name    : TailRiskSharing.VaRConv.display14_varR_varL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:01.207646+00:00
-- url     : https://prove2.me/theorems/51c1727e-546e-4231-9f2e-e270a21d19a4
-- title:
--   (14), p. 10 — VaR^R_{α₁} □ VaR^L_{α₂} = VaR^R_{α₁+α₂}
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, and let $\alpha_1,\alpha_2>0$ with $\alpha_1+\alpha_2<1$. For every random variable $X$,
--
--   $$\mathrm{VaR}^R_{\alpha_1}\,\square\,\mathrm{VaR}^L_{\alpha_2}(X)=\mathrm{VaR}^R_{\alpha_1+\alpha_2}(X).$$
--
--   One right and one left quantile combine to a right quantile at the summed level. This is the first mixed case of the proof of Theorem 1(i), from which the remaining pairs of (8) follow.
--
--   **Formalization Note** The domain is $L^0$; the inf-convolution is computed in $[-\infty,\infty]$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 10, proof of Theorem 1(i), display (14)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem display14_varR_varL {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα : α₁ + α₂ < 1)
    (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    infConv L0 ![VaRR P α₁, VaRL P α₂] X = ((VaRR P (α₁ + α₂) X : ℝ) : EReal) := by sorry

end TailRiskSharing.VaRConv
