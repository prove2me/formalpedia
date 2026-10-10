-- Prove2me | Theorems.Thm_TailRiskSharing_RobustVaR_display39_upper_bound
-- name    : TailRiskSharing.RobustVaR.display39_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:04:50.024381+00:00
-- url     : https://prove2.me/theorems/10050707-1b71-4e3c-a0de-611c11818865
-- title:
--   (39), p. 31 — V_{δ₁} ⊞ V_{δ₂}(X) ≤ V_{δ₁}(X) + δ₂/α via the allocation (X + δ₂/α, −δ₂/α)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be atomless, $\alpha\in(0,1)$, $X\in L^\infty$ and $0<\delta_1\le\delta_2$. Write $V_\delta=[\mathrm{VaR}^L_\alpha]^1_\delta$ for the robust left VaR over the order-$1$ Wasserstein ball of radius $\delta$, and set $X^*_1=X+\delta_2/\alpha$, $X^*_2=-\delta_2/\alpha$. Then
--
--   1. $(X^*_1,X^*_2)$ is a comonotonic allocation of $X$;
--   2. $V_{\delta_1}(X^*_1)=V_{\delta_1}(X)+\delta_2/\alpha$;
--   3. $V_{\delta_2}(X^*_2)=0$;
--   4. consequently
--
--   $$
--   V_{\delta_1}\boxplus V_{\delta_2}(X)\le V_{\delta_1}(X)+\frac{\delta_2}{\alpha}.
--   $$
--
--   This is the easy half of the two-agent identity (38): giving all the risk to the agent with the smaller uncertainty radius, plus a cash transfer, achieves the claimed value.
--
--   **Formalization Note** The paper prints "$V_{\delta_2}(X^*_1)=0$"; the intended claim, stated here, is $V_{\delta_2}(X^*_2)=0$ for the constant $X^*_2=-\delta_2/\alpha$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 31, proof of Theorem 6(i), display (39) and the sentence before it

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem display39_upper_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (X : Ω → ℝ) (hX : X ∈ TailRiskSharing.TailConv.Linf P)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁₂ : δ₁ ≤ δ₂) :
    (![fun ω => X ω + δ₂ / α, fun _ => -δ₂ / α] : Fin 2 → Ω → ℝ) ∈
        TailRiskSharing.ComonoConv.ComonoAllocations P (TailRiskSharing.TailConv.Linf P) 2 X ∧
      robust P 1 δ₁ (TailRiskSharing.VaRConv.VaRL P α) (fun ω => X ω + δ₂ / α) = robust P 1 δ₁ (TailRiskSharing.VaRConv.VaRL P α) X + δ₂ / α ∧
      robust P 1 δ₂ (TailRiskSharing.VaRConv.VaRL P α) (fun _ => -δ₂ / α) = 0 ∧
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) ![robust P 1 δ₁ (TailRiskSharing.VaRConv.VaRL P α), robust P 1 δ₂ (TailRiskSharing.VaRConv.VaRL P α)] X ≤
        ((robust P 1 δ₁ (TailRiskSharing.VaRConv.VaRL P α) X + δ₂ / α : ℝ) : EReal) := by sorry

end TailRiskSharing.RobustVaR
