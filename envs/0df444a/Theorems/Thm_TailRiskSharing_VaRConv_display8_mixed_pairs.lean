-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_display8_mixed_pairs
-- name    : TailRiskSharing.VaRConv.display8_mixed_pairs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:18:58.328672+00:00
-- url     : https://prove2.me/theorems/90ee884c-51ca-4def-9ef8-d54f929eab73
-- title:
--   (8), p. 9 — VaR^L □ VaR^R = VaR^R □ VaR^L = VaR^R □ VaR^R = VaR^R_{α₁+α₂}
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, and let $\alpha_1,\alpha_2>0$ with $\alpha_1+\alpha_2<1$. For every random variable $X$,
--
--   $$\mathrm{VaR}^L_{\alpha_1}\,\square\,\mathrm{VaR}^R_{\alpha_2}(X)=\mathrm{VaR}^R_{\alpha_1}\,\square\,\mathrm{VaR}^L_{\alpha_2}(X)=\mathrm{VaR}^R_{\alpha_1}\,\square\,\mathrm{VaR}^R_{\alpha_2}(X)=\mathrm{VaR}^R_{\alpha_1+\alpha_2}(X).$$
--
--   As soon as one of two agents uses a right quantile, the inf-convolution is a right quantile at the summed level. Together with (7) this covers every pair of VaRs, and it shows that left and right quantiles play asymmetric roles in risk sharing.
--
--   **Formalization Note** The domain is $L^0$; each inf-convolution is computed in $[-\infty,\infty]$. The three equalities are stated as a conjunction of three identities with the common right-hand side.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 9, display (8); proof p. 10

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem display8_mixed_pairs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα : α₁ + α₂ < 1)
    (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    infConv L0 ![VaRL P α₁, VaRR P α₂] X = ((VaRR P (α₁ + α₂) X : ℝ) : EReal) ∧
    infConv L0 ![VaRR P α₁, VaRL P α₂] X = ((VaRR P (α₁ + α₂) X : ℝ) : EReal) ∧
    infConv L0 ![VaRR P α₁, VaRR P α₂] X = ((VaRR P (α₁ + α₂) X : ℝ) : EReal) := by sorry

end TailRiskSharing.VaRConv
