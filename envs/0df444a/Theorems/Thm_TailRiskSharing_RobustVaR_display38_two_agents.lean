-- Prove2me | Theorems.Thm_TailRiskSharing_RobustVaR_display38_two_agents
-- name    : TailRiskSharing.RobustVaR.display38_two_agents
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:03:12.159992+00:00
-- url     : https://prove2.me/theorems/2f1e92a5-fea7-4a71-9137-7babd2c7c8e6
-- title:
--   (38), p. 31 — two agents: V_{δ₁} ⊞ V_{δ₂}(X) = V_{δ₁}(X) + δ₂/α for δ₁ ≤ δ₂
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be atomless, $\alpha\in(0,1)$, $X\in L^\infty$ and $0<\delta_1\le\delta_2$. Write $V_\delta=[\mathrm{VaR}^L_\alpha]^1_\delta$ for the robust left VaR over the order-$1$ Wasserstein ball of radius $\delta$, and $\boxplus$ for the inf-convolution over comonotonic allocations. Then
--
--   $$
--   V_{\delta_1}\boxplus V_{\delta_2}(X)=V_{\delta_1}(X)+\frac{\delta_2}{\alpha}.
--   $$
--
--   This is the two-agent case of Theorem 6(i); the general case follows from it by induction on the number of agents.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 31, proof of Theorem 6(i), display (38); proof pp. 31–32

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem display38_two_agents {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (X : Ω → ℝ) (hX : X ∈ TailRiskSharing.TailConv.Linf P)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁₂ : δ₁ ≤ δ₂) :
    TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) ![robust P 1 δ₁ (TailRiskSharing.VaRConv.VaRL P α), robust P 1 δ₂ (TailRiskSharing.VaRConv.VaRL P α)] X =
      ((robust P 1 δ₁ (TailRiskSharing.VaRConv.VaRL P α) X + δ₂ / α : ℝ) : EReal) := by sorry

end TailRiskSharing.RobustVaR
