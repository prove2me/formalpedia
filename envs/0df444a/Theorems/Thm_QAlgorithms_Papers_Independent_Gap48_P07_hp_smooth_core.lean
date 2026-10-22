-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_hp_smooth_core
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.hp_smooth_core
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:13:53.25957+00:00
-- url     : https://prove2.me/theorems/09d250ef-007b-4f83-878f-566913e75279
-- title:
--   Lemma 2.1.
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup on a complex Banach space $X$, and let $f(A)$ be its extended Hille–Phillips value. For every integer $n\ge1$, define
--   $$I=\{x\in\operatorname{dom}A^n\cap\operatorname{dom}f(A):f(A)x\in\operatorname{dom}A^n\}.$$
--   Then $I$ is a core: the closure in $X\times X$ of the graph of $f(A)$ restricted to $I$ is the full graph of $f(A)$. This records graph approximation, rather than norm density alone.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 5, Lemma 2.1.

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

/-- PDF p.5, Lemma 2.1: membership and output conditions both define the core. -/
theorem hp_smooth_core (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (f : ℂ → ℂ) (hf : HPRegularizable T f) (n : ℕ) (hn : 1 ≤ n) :
    GraphCore (hpGraph T f) {x | x ∈ graphDomain (graphPower (negativeGenerator T) n) ∧
      x ∈ graphDomain (hpGraph T f) ∧ graphValue (hpGraph T f) x ∈
        graphDomain (graphPower (negativeGenerator T) n)} := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
