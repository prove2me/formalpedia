-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_bernstein_rate_bounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.bernstein_rate_bounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:20:50.24808+00:00
-- url     : https://prove2.me/theorems/4ced1214-40ac-4d88-9132-0e334d91c44b
-- title:
--   Lemma 4.1.
-- statement:
--   Let $g\sim(a,b,\mu)$ be a Bernstein function and $r=r[g]$. For every $t>0$ and every complex $z$ with $\Re z>0$,
--   $$(t\Re z)e^{-t\Re z}r(t)\le\Re g(z)\le|g(z)|\le\max(2,t|z|)r(t).$$
--   The three estimates relate the rate to values in the open right halfplane, retaining the real part in the lower bound.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 17, Lemma 4.1.

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

/-- PDF pp.17–18, Lemma 4.1: all three inequalities, including the real part. -/
theorem bernstein_rate_bounds (g : BernsteinData) (t : ℝ) (ht : 0 < t)
    (z : ℂ) (hz : 0 < z.re) :
    (t * z.re) * Real.exp (-(t * z.re)) * bernsteinRate g t ≤ (bernsteinValue g z).re ∧
    (bernsteinValue g z).re ≤ ‖bernsteinValue g z‖ ∧
    ‖bernsteinValue g z‖ ≤ max 2 (t * ‖z‖) * bernsteinRate g t := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
