-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_general_rate_sharpness
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.general_rate_sharpness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:23:24.885501+00:00
-- url     : https://prove2.me/theorems/b46b2148-5d63-4098-af67-68d34d52f6e1
-- title:
--   Remark 4.8.
-- statement:
--   Let $g$ be a Bernstein function with rate $r$ and $tr(t)\to\infty$, and let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$. Suppose that, for some $0\le\theta<\pi/2$, nonzero points of $\sigma(A)\cap\{z:\Re z>0,\ |\arg z|\le\theta\}$ accumulate at zero. Then every positive nonincreasing $\epsilon(t)\to0$ admits $y\in\operatorname{ran}g(A)$ with
--   $$\sup_{t\ge1}\frac{\|C_t(A)y\|}{\epsilon(t)r(t)}=+\infty.$$
--   The same full conclusion holds if $T$ consists of isometries and some positive-time member is not surjective, or if there is a closed invariant complex linear subspace on which these two properties hold. The subspace version is expressed through the actual action of $T$ on that subspace, without asserting spectrum inclusion for arbitrary restrictions. This extends sharpness beyond special Bernstein functions.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 21, Remark 4.8.

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

/-- PDF p.21, Remark 4.8: full sector result and both isometry consequences,
including a closed invariant subspace; no arbitrary restriction-spectrum inclusion. -/
theorem general_rate_sharpness (g : BernsteinData)
    (hr : Tendsto (fun t => t * bernsteinRate g t) atTop atTop)
    (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) :
    ((∃ theta : ℝ, 0 ≤ theta ∧ theta < Real.pi / 2 ∧
      SpectralAccumulation T {z | 0 < z.re ∧ |z.arg| ≤ theta}) →
      SharpRate T (hpGraph T (bernsteinValue g)) (bernsteinRate g)) ∧
    (((∀ t : ℝ, 0 ≤ t → ∀ x : X, ‖T t x‖ = ‖x‖) ∧
      ∃ t : ℝ, 0 < t ∧ ¬ Function.Surjective (T t)) →
      SharpRate T (hpGraph T (bernsteinValue g)) (bernsteinRate g)) ∧
    ((∃ Y : Submodule ℂ X, IsClosed (Y : Set X) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x ∈ Y, T t x ∈ Y ∧ ‖T t x‖ = ‖x‖) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ y ∈ Y, ∀ x ∈ Y, T t x ≠ y) →
      SharpRate T (hpGraph T (bernsteinValue g)) (bernsteinRate g)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
