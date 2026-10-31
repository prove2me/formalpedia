-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hellinger_order_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hellinger_order_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:48:43.863084+00:00
-- url     : https://prove2.me/theorems/556d427c-2509-46ff-a799-7fefd65703f6
-- title:
--   Theorem 36: H_alpha is increasing for alpha>0; (1/alpha-1)H_alpha is decreasing for 0<alpha<1; H_alpha/alpha is log-convex for alpha>0, implying H_((alpha+beta)/2)^2<=(alpha+beta)^2 H_alpha H_beta/(4a
-- statement:
--   For any probability pair, $H_\alpha(P\|Q)$ is increasing for $\alpha>0$, while $(1/\alpha-1)H_\alpha(P\|Q)$ is decreasing for $0<\alpha<1$. Moreover $H_\alpha/\alpha$ is log-convex: for $a,c>0$ and $0\le t\le1$,
--
--   $$\frac{H_{(1-t)a+tc}}{(1-t)a+tc}\le
--   \left(\frac{H_a}{a}\right)^{1-t}\left(\frac{H_c}{c}\right)^t.$$
--
--   In particular $H_{(a+c)/2}^2\le (a+c)^2H_aH_c/(4ac)$. The multiplicative formulation includes $P=Q$ without taking the logarithm of zero; $H_1$ is KL in nats.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 68, Theorem 36

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 36: H_alpha is increasing for alpha>0; (1/alpha-1)H_alpha is decreasing for 0<alpha<1; H_alpha/alpha is log-convex for alpha>0, implying H_((alpha+inverseUpperDensity)/2)^2<=(alpha+inverseUpperDensity)^2 H_alpha H_beta/(4alpha inverseUpperDensity). Sason--Verdu, arXiv:1508.00335v7, PDF p.68.  -/
theorem hellinger_order_properties
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    MonotoneOn (fun a : ℝ => hellinger a P Q) (Ioi 0) ∧
    AntitoneOn (fun a : ℝ => ENNReal.ofReal (1 / a - 1) * hellinger a P Q) (Ioo 0 1) ∧
    (∀ a c t : ℝ, 0 < a → 0 < c → 0 ≤ t → t ≤ 1 →
      hellinger ((1 - t) * a + t * c) P Q / ENNReal.ofReal ((1 - t) * a + t * c) ≤
        (hellinger a P Q / ENNReal.ofReal a) ^ (1 - t) *
          (hellinger c P Q / ENNReal.ofReal c) ^ t) ∧
    (∀ a c : ℝ, 0 < a → 0 < c → hellinger ((a + c) / 2) P Q ^ 2 ≤
      ENNReal.ofReal ((a + c) ^ 2 / (4 * a * c)) * hellinger a P Q * hellinger c P Q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
