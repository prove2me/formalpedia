-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_hp_bounded_factor_product
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.hp_bounded_factor_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:13:26.282995+00:00
-- url     : https://prove2.me/theorems/b897eb9e-6bc2-47cd-a0bd-aab4b2656b17
-- title:
--   §2.2, equation (2.3): HP bounded-factor product rule
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup on a complex Banach space. Let $f$ be regularizable in its extended Hille–Phillips calculus and let $g\in A_+^1$ be elementary. Then $fg$ is regularizable and, with natural product domains,
--   $$g(A)f(A)\subseteq f(A)g(A)=(fg)(A),\qquad (fg)(A)\in\mathcal L(X)\ \Longleftrightarrow\ \operatorname{ran}g(A)\subseteq\operatorname{dom}f(A).$$
--   Inclusion is graph inclusion and the range is the actual range. This is the bounded-factor rule; no equality for two arbitrary unbounded symbols is asserted.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 5, §2.2, equation (2.3): HP bounded-factor product rule

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

/-- PDF p.5, (2.3): only the second symbol is elementary. Natural product
 domains and the final boundedness equivalence are both retained. -/
theorem hp_bounded_factor_product (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (f g : ℂ → ℂ) (hf : HPRegularizable T f) (hg : LaplaceImage g) :
    HPRegularizable T (f * g) ∧
    graphMul (hpGraph T g) (hpGraph T f) ⊆ graphMul (hpGraph T f) (hpGraph T g) ∧
    graphMul (hpGraph T f) (hpGraph T g) = hpGraph T (f * g) ∧
    (Bounded (hpGraph T (f * g)) ↔ graphRange (hpGraph T g) ⊆ graphDomain (hpGraph T f)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
