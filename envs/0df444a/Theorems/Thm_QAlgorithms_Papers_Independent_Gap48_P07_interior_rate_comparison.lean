-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_interior_rate_comparison
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.interior_rate_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:21:12.011544+00:00
-- url     : https://prove2.me/theorems/135ae968-0992-4650-a2e5-a8ad13083222
-- title:
--   Proposition 4.2.
-- statement:
--   For every $0<\alpha\le\beta<\infty$, there are $c_0,c_1>0$, depending only on $\alpha,\beta$, such that for every Bernstein function $g$ with associated rate $r$, every $t>0$, and every $z$ with $\Re z>0$ satisfying $\alpha\le t\Re z\le t|z|\le\beta$,
--   $$c_0r(t)\le|g(z)|\le c_1r(t).$$
--   The constants are uniform in $g,t,z$. This comparison recovers rates from suitably chosen values of the symbol.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 18, Proposition 4.2.

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

/-- PDF p.18, Proposition 4.2: constants precede g,t,z. -/
theorem interior_rate_comparison (alpha beta : ℝ) (ha : 0 < alpha) (hab : alpha ≤ beta) :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧ ∀ (g : BernsteinData) (t : ℝ) (z : ℂ),
      0 < t → 0 < z.re → alpha ≤ t * z.re → t * z.re ≤ t * ‖z‖ → t * ‖z‖ ≤ beta →
      c0 * bernsteinRate g t ≤ ‖bernsteinValue g z‖ ∧ ‖bernsteinValue g z‖ ≤ c1 * bernsteinRate g t := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
