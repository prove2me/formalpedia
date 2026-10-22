-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_general_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.general_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:19:37.449266+00:00
-- url     : https://prove2.me/theorems/9c06d004-8176-49d2-9d5e-83565ca85ae3
-- title:
--   Theorem 3.4.
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$, let $M=\sup_{s\ge0}\|T(s)\|$, and let $g\sim(a,b,\mu)$ be a Bernstein function with associated rate $r(t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$. For every $x\in\operatorname{dom}g(A)$ and $y=g(A)x$,
--   $$\|C_t(A)y\|\le2Mr(t)\|x\|\qquad(t>0).$$
--   If $tr(t)\to\infty$, $g(0+)=0$, and $T$ is mean ergodic, then $\|C_t(A)y\|=o(r(t))$ for every $y\in\operatorname{ran}g(A)$. If $tr(t)=O(1)$, then $\operatorname{ran}g(A)\subseteq\operatorname{ran}A$ and $\|C_t(A)y\|=O(t^{-1})$ for every such $y$. Ranges are actual ranges, and asymptotic constants may depend on the vector. These are all three parts of the main general estimate.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 16, Theorem 3.4.

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

/-- PDF pp.16–17, Theorem 3.4: all (a)–(c), without global density or injectivity. -/
theorem general_rate (g : BernsteinData) (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) :
    GeneralRateConclusion g T := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
