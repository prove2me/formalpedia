-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_Supplement_theorem4_iii_convex_order
-- name    : TailRiskSharing.VaRConv.Supplement.theorem4_iii_convex_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:44:38.229785+00:00
-- url     : https://prove2.me/theorems/735ea96b-23e1-44c8-a491-050701d877d9
-- title:
--   Theorem 4 (iii) — equality of inf-convolutions and the maximal tail parameter
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space and $\mathcal X$ any convex cone of measurable real random variables containing $L^\infty$, closed under equality in law and taking upper tails. Let $n\geq1$. For each agent $i$, let $0<\varepsilon_i<1$ and let $\rho_i:\mathcal X\to\mathbb R$ be an $\varepsilon_i$-tail risk measure that is convex-order consistent. Write $\varepsilon=\max_i\varepsilon_i$. Then
--
--   $$\square_{i=1}^n\rho_i(X)=\boxplus_{i=1}^n\rho_i(X)\quad\text{for every }X\in\mathcal X,$$
--
--   and $\square_i\rho_i$ is an $\varepsilon$-tail risk measure: it takes equal extended-real values on any two variables in $\mathcal X$ having the same upper $\varepsilon$-tail law.
--
--   This retains both conclusions of Theorem 4(iii). The comonotonic constraint is exactly (22), and neither monetary behavior nor convexity, continuity, normalization or boundedness is added. Real-valued individual agents follow the risk-sharing convention on p. 7; their infima may equal $-\infty$.
--
--   Differences from the source:
--   - encoding: a convex cone of random variables, law and tail closed; allocations sum to X → IsSourceDomain with measurable representatives, tail CDF (6), and published pointwise allocations; reason: the source works modulo null sets; law closure includes changes of representatives, so no source instance is lost.
--   - reading: convex test expectations provided both exist → signed extended expectations with infinity-minus-infinity excluded; reason: allows one-sided infinite expectations without adding moments or using nonintegrable Bochner defaults.
--   - encoding: epsilon is the maximum of finitely many positive levels → sSup of the range of epsilon_i, with 1 <= n; reason: the range is finite, bounded and nonempty, so the real supremum is its maximum.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 20–21, Theorem 4(iii); proof p. 21

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone
import Definitions.Def_TailRiskSharing_VaRConv_Supplement_Domain
import Definitions.Def_TailRiskSharing_VaRConv_Supplement_ConvexOrder

namespace TailRiskSharing.VaRConv.Supplement

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Theorem 4(iii), pp.20–21: both conclusions on the full source domain. -/
theorem theorem4_iii_convex_order
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (dom : Set (Ω → ℝ)) (hdom : IsSourceDomain P dom)
    {n : ℕ} (hn : 1 ≤ n) (εs : Fin n → ℝ)
    (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (ρ : Fin n → (Ω → ℝ) → ℝ)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P dom (εs i) (ρ i))
    (hcx : ∀ i, IsConvexOrderConsistent P dom (ρ i)) :
    (∀ X ∈ dom, infConv dom ρ X = TailRiskSharing.ComonoConv.comonoInfConv P dom ρ X) ∧
    TailRiskSharing.VaRTail.IsTailRiskMeasureE P dom (sSup (Set.range εs)) (infConv dom ρ)
    := by sorry

end TailRiskSharing.VaRConv.Supplement
