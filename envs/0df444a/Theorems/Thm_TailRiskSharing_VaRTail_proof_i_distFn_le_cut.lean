-- Prove2me | Theorems.Thm_TailRiskSharing_VaRTail_proof_i_distFn_le_cut
-- name    : TailRiskSharing.VaRTail.proof_i_distFn_le_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:58.146721+00:00
-- url     : https://prove2.me/theorems/ee101b0b-2bf7-4855-b05d-0ec8b38c72cc
-- title:
--   Proof of Theorem 2(i), p. 14 — F_{X−Y}(x) ≤ F_{X^[α]}(x) for x ≥ VaR^R_{α+ε}(X) when VaR^L_α(Y) = 0
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $\varepsilon\in(0,1)$ and $\alpha\in(0,1-\varepsilon)$. Let $X$ be a random variable, $U$ a uniform random variable on $[0,1]$ with $F^{-1}_X(U)=X$ a.s., and $X^{[\alpha]}=X\,\mathbb 1_{\{U\le 1-\alpha\}}+\mathrm{VaR}^R_{\alpha+\varepsilon}(X)\,\mathbb 1_{\{U>1-\alpha\}}$. If $Y$ is a random variable with $\mathrm{VaR}^L_\alpha(Y)=0$, then
--   $$F_{X-Y}(x)\le F_{X^{[\alpha]}}(x)\qquad\text{for all } x\ge \mathrm{VaR}^R_{\alpha+\varepsilon}(X).$$
--
--   This comparison is the key step of the lower bound $\rho(X^{[\alpha]})\le \mathrm{VaR}^L_\alpha\,\square\,\rho(X)$ in Theorem 2(i): no allocation that gives the VaR agent a position of VaR zero leaves the other agent with a lighter $\varepsilon$-tail than $X^{[\alpha]}$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 14, proof of Theorem 2(i), displayed comparison

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

open MeasureTheory Filter Topology

namespace TailRiskSharing.VaRTail

theorem proof_i_distFn_le_cut {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (U : Ω → ℝ) (hU : IsQuantileUniform P X U)
    (Y : Ω → ℝ) (hY : Y ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (hYvar : TailRiskSharing.VaRConv.VaRL P α Y = 0)
    (x : ℝ) (hx : TailRiskSharing.VaRConv.VaRR P (α + ε) X ≤ x) :
    TailRiskSharing.VaRConv.distFn P (X - Y) x ≤ TailRiskSharing.VaRConv.distFn P (cutAt P ε α X U) x := by sorry

end TailRiskSharing.VaRTail
