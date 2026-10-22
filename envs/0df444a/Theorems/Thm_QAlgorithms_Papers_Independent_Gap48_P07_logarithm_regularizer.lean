-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_logarithm_regularizer
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.logarithm_regularizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:24:58.76135+00:00
-- url     : https://prove2.me/theorems/22a3d50a-0738-4eeb-8c97-63aac68b5229
-- title:
--   §5, unnumbered operator logarithm regularizer
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space. With principal logarithm and the removable value of $\log z/(z-1)$ at one, the four symbols $z\log z/((z-1)(1+z))$, $(z-1)/(z+1)$, $z\log z/(1+z)^2$, and $e(z)=z/(1+z)^2$ belong to $A_+^1$. If $A$ is injective, then
--   $$e\text{ is a regularizer for }\log z,\qquad \log A\text{ is defined in the extended HP calculus}.$$
--   Both elementary values are evaluated by the actual integral calculus of $T$. The source singles out this regularizer; it does not assert a family of product rules indexed by every real $k>0$.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 22, §5, unnumbered operator logarithm regularizer

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

/-- PDF p.22: elementary memberships and the source's actual regularizer
z/(1+z)^2 for the principal logarithm, under injectivity of A. -/
theorem logarithm_regularizer (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) :
    LaplaceImage (fun z => z * logarithmicStieltjes z / (1 + z)) ∧
    LaplaceImage (fun z : ℂ => (z - 1) / (z + 1)) ∧
    LaplaceImage (fun z : ℂ => z * Complex.log z / (1 + z) ^ 2) ∧
    LaplaceImage logRegularizer ∧
    (InjectiveGraph (negativeGenerator T) → HPRegularizer T Complex.log logRegularizer ∧
      HPRegularizable T Complex.log) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
