-- Prove2me | Theorems.Thm_TailRiskSharing_VaRTail_display17_distFn_cut
-- name    : TailRiskSharing.VaRTail.display17_distFn_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:59.661967+00:00
-- url     : https://prove2.me/theorems/60bd46b9-0d29-47b4-9d1b-f683146cd499
-- title:
--   (17), p. 13 — the distribution function of X^[α]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $\varepsilon\in(0,1)$ and $\alpha\in(0,1-\varepsilon)$. Let $X$ be a random variable, $U$ a uniform random variable on $[0,1]$ with $F^{-1}_X(U)=X$ a.s., and
--   $$X^{[\alpha]}=X\,\mathbb 1_{\{U\le 1-\alpha\}}+\mathrm{VaR}^R_{\alpha+\varepsilon}(X)\,\mathbb 1_{\{U>1-\alpha\}}.$$
--   Then for every $x\in\mathbb R$,
--   $$\mathbb P(X^{[\alpha]}\le x)=\begin{cases}F_X(x), & x<\mathrm{VaR}^R_{\alpha+\varepsilon}(X),\\ F_X(x)+\alpha, & \mathrm{VaR}^R_{\alpha+\varepsilon}(X)\le x<\mathrm{VaR}^L_\alpha(X),\\ 1, & x\ge \mathrm{VaR}^L_\alpha(X).\end{cases}$$
--
--   The formula shows that the law of $X^{[\alpha]}$ does not depend on the choice of $U$; it is used throughout the proof of Theorem 2.
--
--   **Formalization Note** The three cases are encoded with nested `if … then … else` on `x < VaR^R_{α+ε}(X)` and `x < VaR^L_α(X)`.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 13, proof of Theorem 2, display (17)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

open MeasureTheory Filter Topology

namespace TailRiskSharing.VaRTail

theorem display17_distFn_cut {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (U : Ω → ℝ) (hU : IsQuantileUniform P X U)
    (x : ℝ) :
    TailRiskSharing.VaRConv.distFn P (cutAt P ε α X U) x =
      if x < TailRiskSharing.VaRConv.VaRR P (α + ε) X then TailRiskSharing.VaRConv.distFn P X x
      else if x < TailRiskSharing.VaRConv.VaRL P α X then TailRiskSharing.VaRConv.distFn P X x + α
      else 1 := by sorry

end TailRiskSharing.VaRTail
