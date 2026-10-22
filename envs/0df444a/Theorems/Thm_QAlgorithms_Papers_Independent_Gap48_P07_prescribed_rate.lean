-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_prescribed_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.prescribed_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:20:13.71399+00:00
-- url     : https://prove2.me/theorems/3974e15d-592f-4027-ba2a-55ae36e9a5bc
-- title:
--   Corollary 3.5.
-- statement:
--   Let $r:(0,\infty)\to(0,\infty)$ be such that $tr(t)$ is nondecreasing and concave. There exists a Bernstein function $g$ depending only on $r$, with $r=r[g]$, such that for every complex Banach space and every bounded strongly continuous semigroup $T$ on it, with negative generator $A$ and bound $M$,
--   $$\|C_t(A)g(A)x\|\le2Mr(t)\|x\|\quad(x\in\operatorname{dom}g(A),\ t>0).$$
--   If $tr(t)\to\infty$, $g(0+)=0$, and $T$ is mean ergodic, then $\|C_t(A)y\|=o(r(t))$ for every $y\in\operatorname{ran}g(A)$. If $tr(t)=O(1)$, then $\operatorname{ran}g(A)\subseteq\operatorname{ran}A$ and $\|C_t(A)y\|=O(t^{-1})$ on that range. The single witness $g$ precedes all semigroups; all three conclusions of Theorem 3.4 are retained.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 17, Corollary 3.5.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07

noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)

open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- PDF p.17, Corollary 3.5: g is chosen before the space and the semigroup. -/
theorem prescribed_rate (r : ℝ → ℝ) (hr : ∀ t, 0 < t → 0 < r t)
    (hm : MonotoneOn (fun t => t * r t) (Ioi 0))
    (hc : ConcaveOn ℝ (Ioi 0) (fun t => t * r t)) :
    ∃ g : BernsteinData, (∀ t, 0 < t → r t = bernsteinRate g t) ∧
      ∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
        (T : ℝ → Y →L[ℂ] Y), BoundedC0 T → GeneralRateConclusion g T := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
