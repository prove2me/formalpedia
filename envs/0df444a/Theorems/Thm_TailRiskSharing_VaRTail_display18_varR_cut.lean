-- Prove2me | Theorems.Thm_TailRiskSharing_VaRTail_display18_varR_cut
-- name    : TailRiskSharing.VaRTail.display18_varR_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:46.881701+00:00
-- url     : https://prove2.me/theorems/34df960d-bb3a-41cc-a4d3-cca25ce09e95
-- title:
--   (18), p. 13 — VaR^R_ε(X^[α]) = VaR^R_{α+ε}(X)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $\varepsilon\in(0,1)$ and $\alpha\in(0,1-\varepsilon)$. Let $X$ be a random variable, $U$ a uniform random variable on $[0,1]$ with $F^{-1}_X(U)=X$ a.s., and $X^{[\alpha]}=X\,\mathbb 1_{\{U\le 1-\alpha\}}+\mathrm{VaR}^R_{\alpha+\varepsilon}(X)\,\mathbb 1_{\{U>1-\alpha\}}$. Then
--   $$\mathrm{VaR}^R_\varepsilon\big(X^{[\alpha]}\big)=\mathrm{VaR}^R_{\alpha+\varepsilon}(X).$$
--
--   Together with display (17) this locates the $\varepsilon$-tail of $X^{[\alpha]}$, which is all an $\varepsilon$-tail risk measure sees.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 13, proof of Theorem 2, display (18)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

open MeasureTheory Filter Topology

namespace TailRiskSharing.VaRTail

theorem display18_varR_cut {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (U : Ω → ℝ) (hU : IsQuantileUniform P X U) :
    TailRiskSharing.VaRConv.VaRR P ε (cutAt P ε α X U) = TailRiskSharing.VaRConv.VaRR P (α + ε) X := by sorry

end TailRiskSharing.VaRTail
