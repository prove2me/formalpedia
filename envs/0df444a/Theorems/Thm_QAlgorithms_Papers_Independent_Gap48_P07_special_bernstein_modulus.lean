-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_special_bernstein_modulus
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.special_bernstein_modulus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:17:18.613541+00:00
-- url     : https://prove2.me/theorems/2f132099-b5fc-4ba5-b407-9bf6fe92cbd5
-- title:
--   Theorem 2.8.
-- statement:
--   Let $g$ be a nonzero special Bernstein function, meaning that both $g$ and $z/g(z)$ are Bernstein functions. Use its canonical continuous boundary extension, so $g(0)=g(0+)$. For every $z\in\mathbb C$ with $\Re z\ge0$,
--   $$\frac{|g(z)|}{3e}\le g(|z|)\le3e|g(z)|.$$
--   Here $e=\exp(1)$. The closed-halfplane estimate includes nonzero constant functions and the point $z=0$.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 10, Theorem 2.8.

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

/-- PDF p.10, Theorem 2.8: exact 3e factor on the closed halfplane. -/
theorem special_bernstein_modulus (g : BernsteinData)
    (hg : SpecialBernstein (bernsteinValue g)) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖bernsteinValue g z‖ / (3 * Real.exp 1) ≤ (bernsteinValue g (‖z‖ : ℂ)).re ∧
    (bernsteinValue g (‖z‖ : ℂ)).re ≤ 3 * Real.exp 1 * ‖bernsteinValue g z‖ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
