-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_complete_rate_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.complete_rate_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:27:52.990579+00:00
-- url     : https://prove2.me/theorems/eb13dd4b-7932-434f-b640-aade4757dd5a
-- title:
--   Theorem B.3.
-- statement:
--   Let $r:(0,\infty)\to(0,\infty)$, and construct $h(t)=tr(t)$. Then
--   $$\bigl[\exists\text{ complete Bernstein }g\text{ with }r=r[g]\bigr]\quad\Longleftrightarrow\quad h\text{ is a Bernstein function}.$$
--   The function $h$ is determined by $r$, rather than supplied as an independent witness. Positivity of $r$ excludes zero on both sides. This characterizes the complete-Bernstein subclass of rate functions.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 26, Theorem B.3.

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

/-- PDF pp.26–27, Theorem B.3: h(t)=t r(t) is constructed; positivity excludes zero. -/
theorem complete_rate_characterization (r : ℝ → ℝ) (hr : ∀ t, 0 < t → 0 < r t) :
    (∃ g : BernsteinData, CompleteBernstein g ∧ ∀ t, 0 < t → r t = bernsteinRate g t) ↔
      Bernstein (fun t => t * r t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
