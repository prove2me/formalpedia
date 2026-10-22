-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_rate_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.rate_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:19:13.102089+00:00
-- url     : https://prove2.me/theorems/3cd1cbc4-edd7-4e04-b153-a3a5b7a39de0
-- title:
--   Theorem 3.2.
-- statement:
--   Let $r:(0,\infty)\to(0,\infty)$. There is a nonzero Bernstein function $g\sim(a,b,\mu)$ with $r=r[g]$ if and only if $t\mapsto tr(t)$ is strictly positive, nondecreasing, and concave. For every such representing $g$, $r$ is continuous and nonincreasing and
--   $$\lim_{t\to\infty}r(t)=a/2,\qquad\lim_{t\downarrow0}tr(t)=b.$$
--   Moreover, $tr(t)$ is bounded on the positive axis if and only if $a=0$ and $g(z)=zh(z)$ for some $h\in A_+^1$; each such $h$ is completely monotone on the positive axis. Constants and linear Bernstein functions are allowed. The result characterizes precisely the possible rate functions.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 14, Theorem 3.2.

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

/-- PDF pp.14–16, Theorem 3.2: equivalence and all supplementary clauses
for every representing g, including constants and linear functions. -/
theorem rate_characterization (r : ℝ → ℝ) (hr : ∀ t, 0 < t → 0 < r t) :
    ((∃ g : BernsteinData, NonzeroBernstein g ∧ ∀ t, 0 < t → r t = bernsteinRate g t) ↔
      (∀ t, 0 < t → 0 < t * r t) ∧ MonotoneOn (fun t => t * r t) (Ioi 0) ∧
        ConcaveOn ℝ (Ioi 0) (fun t => t * r t)) ∧
    ∀ g : BernsteinData, (∀ t, 0 < t → r t = bernsteinRate g t) →
      ContinuousOn r (Ioi 0) ∧ AntitoneOn r (Ioi 0) ∧ Tendsto r atTop (𝓝 (g.a / 2)) ∧
      Tendsto (fun t => t * r t) (𝓝[>] 0) (𝓝 g.b) ∧
      (BddAbove ((fun t => t * r t) '' Ioi 0) ↔ g.a = 0 ∧ ∃ h : ℂ → ℂ,
        LaplaceImage h ∧ ∀ z : ℂ, 0 < z.re → bernsteinValue g z = z * h z) ∧
      (∀ h : ℂ → ℂ, LaplaceImage h →
        (∀ z : ℂ, 0 < z.re → bernsteinValue g z = z * h z) →
        CompletelyMonotone (fun t : ℝ => (h (t : ℂ)).re)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
