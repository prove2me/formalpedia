-- Prove2me | Theorems.Thm_TailRiskSharing_VaRTail_proof_iv_tail_cut
-- name    : TailRiskSharing.VaRTail.proof_iv_tail_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:57.496521+00:00
-- url     : https://prove2.me/theorems/8ec95880-b616-476b-9686-2ede1083eaf3
-- title:
--   Proof of Theorem 2(iv), p. 15 — Y_{α+ε} =d Z_{α+ε} implies (Y^[α−δ])_ε =d (Z^[α−δ])_ε for δ ∈ [0, α)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $\varepsilon\in(0,1)$ and $\alpha\in(0,1-\varepsilon)$. Let $Y,Z$ be random variables with quantile uniforms $U_Y$, $U_Z$ (uniform on $[0,1]$, $F^{-1}_Y(U_Y)=Y$ and $F^{-1}_Z(U_Z)=Z$ a.s.). For $\beta\in(0,1-\varepsilon)$ write
--   $$Y^{[\beta]}=Y\,\mathbb 1_{\{U_Y\le 1-\beta\}}+\mathrm{VaR}^R_{\beta+\varepsilon}(Y)\,\mathbb 1_{\{U_Y>1-\beta\}},$$
--   and similarly $Z^{[\beta]}$. If the $(\alpha+\varepsilon)$-tails of $Y$ and $Z$ have the same law, $Y_{\alpha+\varepsilon}\overset{d}{=}Z_{\alpha+\varepsilon}$, then for every $\delta\in[0,\alpha)$
--   $$\big(Y^{[\alpha-\delta]}\big)_\varepsilon\overset{d}{=}\big(Z^{[\alpha-\delta]}\big)_\varepsilon .$$
--
--   This is the step that transfers the tail parameter: an $\varepsilon$-tail risk measure cannot distinguish $Y^{[\alpha-\delta]}$ from $Z^{[\alpha-\delta]}$, so the inf-convolutions of Theorem 2 are $(\alpha+\varepsilon)$-tail risk measures.
--
--   **Formalization Note** "$A_p\overset{d}{=}B_p$" is encoded through display (6) as $(F_A(x)-(1-p))_+=(F_B(x)-(1-p))_+$ for all $x$. The truncation at level $\alpha-\delta$ uses $\mathrm{VaR}^R_{\alpha-\delta+\varepsilon}$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 15, proof of Theorem 2(iv), displayed argument

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

open MeasureTheory Filter Topology

namespace TailRiskSharing.VaRTail

theorem proof_iv_tail_cut {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (Y Z : Ω → ℝ) (hY : Y ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (hZ : Z ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)))
    (U V : Ω → ℝ) (hU : IsQuantileUniform P Y U) (hV : IsQuantileUniform P Z V)
    (hYZ : TailEquiv P (α + ε) Y Z) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδα : δ < α) :
    TailEquiv P ε (cutAt P ε (α - δ) Y U) (cutAt P ε (α - δ) Z V) := by sorry

end TailRiskSharing.VaRTail
