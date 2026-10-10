-- Prove2me | Theorems.Thm_TailRiskSharing_RobustVaR_display40_acceptance
-- name    : TailRiskSharing.RobustVaR.display40_acceptance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:02:46.196837+00:00
-- url     : https://prove2.me/theorems/96b42573-1f7c-40a6-b432-40ece3b083c7
-- title:
--   (40), p. 31 — [VaR^L_α]¹_δ(Y) ≤ 0 iff ∫₀^α (−VaR^L_u(Y))₊ du ≥ δ
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be atomless, $\alpha\in(0,1)$ and $\delta>0$, and write $V_\delta(Y)=[\mathrm{VaR}^L_\alpha]^1_\delta(Y)$ for the robust left VaR over the order-$1$ Wasserstein ball of radius $\delta$. For every $Y\in L^\infty$,
--
--   $$
--   V_\delta(Y)\le0\iff\int_0^\alpha\big(-\mathrm{VaR}^L_u(Y)\big)_+\,\mathrm du\ge\delta.
--   $$
--
--   This is the acceptance criterion for the robust VaR with $k=1$: a position is acceptable under model uncertainty exactly when the area of its negative upper-tail quantiles is at least the uncertainty radius. It is the key tool in the proof of the lower bound in Theorem 6.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 31, proof of Theorem 6(i), display (40)

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem display40_acceptance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Y : Ω → ℝ) (hY : Y ∈ TailRiskSharing.TailConv.Linf P) (δ : ℝ) (hδ : 0 < δ) :
    robust P 1 δ (TailRiskSharing.VaRConv.VaRL P α) Y ≤ 0 ↔ δ ≤ ∫ u in (0:ℝ)..α, max (-TailRiskSharing.VaRConv.VaRL P u Y) 0 := by sorry

end TailRiskSharing.RobustVaR
