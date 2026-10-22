-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_bernstein_hp
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.bernstein_hp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:16:51.675104+00:00
-- url     : https://prove2.me/theorems/52378498-d96b-4b57-9245-7d5cf48abcd9
-- title:
--   Corollary 2.6.
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$, and let $g\sim(a,b,\mu)$ be a Bernstein function. Then $g$ is regularizable in the extended Hille–Phillips calculus, $\operatorname{dom}A\subseteq\operatorname{dom}g(A)$, and for $x\in\operatorname{dom}A$,
--   $$g(A)x=ax+bAx+\int_{(0,\infty)}(x-T(s)x)\,\mu(ds).$$
--   The vector integrand is integrable and $\operatorname{dom}A$ is a core for $g(A)$. If $Ax=0$, then $g(A)x=ax$. If $a>0$, the actual range of $g(A)$ is $X$ and its inverse is everywhere defined and bounded. This identifies the Phillips formula with the regularized calculus without assuming that $g(A)$ itself is bounded.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 9, Corollary 2.6.

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

/-- PDF pp.9–10, Corollary 2.6: Phillips formula, core, kernel action and
bounded everywhere inverse when a>0; range means actual range. -/
theorem bernstein_hp (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) (g : BernsteinData) :
    HPRegularizable T (bernsteinValue g) ∧
    graphDomain (negativeGenerator T) ⊆ graphDomain (hpGraph T (bernsteinValue g)) ∧
    (∀ x ∈ graphDomain (negativeGenerator T), Integrable (fun s => x - T s x) g.mu ∧
      (x, (g.a : ℂ) • x + (g.b : ℂ) • graphValue (negativeGenerator T) x +
        ∫ s, x - T s x ∂g.mu) ∈ hpGraph T (bernsteinValue g)) ∧
    GraphCore (hpGraph T (bernsteinValue g)) (graphDomain (negativeGenerator T)) ∧
    (∀ x : X, (x, 0) ∈ negativeGenerator T → (x, (g.a : ℂ) • x) ∈ hpGraph T (bernsteinValue g)) ∧
    (0 < g.a → graphRange (hpGraph T (bernsteinValue g)) = univ ∧
      Bounded (graphInverse (hpGraph T (bernsteinValue g)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
