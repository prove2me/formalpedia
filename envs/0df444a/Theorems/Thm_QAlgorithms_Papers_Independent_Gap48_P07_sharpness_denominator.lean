-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_sharpness_denominator
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.sharpness_denominator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:22:56.424052+00:00
-- url     : https://prove2.me/theorems/ca69d6ff-3f31-4905-b653-ea2e542cc2af
-- title:
--   Remark 4.7.
-- statement:
--   Under the hypotheses of Theorem 4.6, fix a positive nonincreasing $\epsilon(t)\to0$ and $y\in\operatorname{ran}g(A)$. The two assertions are equivalent:
--   $$\sup_{t\ge1}\frac{\|C_t(A)y\|}{\epsilon(t)r[g](t)}=+\infty\quad\Longleftrightarrow\quad\sup_{t\ge1}\frac{\|C_t(A)y\|}{\epsilon(t)g(1/t)}=+\infty.$$
--   Both denominators are positive, and infinite suprema mean unbounded sets of real quotients. This rewrites the sharpness statement using values of the symbol.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 21, Remark 4.7.

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

/-- PDF p.21, Remark 4.7: equivalence of the two unboundedness assertions. -/
theorem sharpness_denominator (g : BernsteinData)
    (hg : SpecialBernstein (bernsteinValue g))
    (hr : Tendsto (fun t => t * bernsteinRate g t) atTop atTop)
    (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) (hacc : SpectralAccumulation T)
    (e : ℝ → ℝ) (he : VanishingFactor e) (y : X)
    (hy : y ∈ graphRange (hpGraph T (bernsteinValue g))) :
    (∀ K : ℝ, ∃ t : ℝ, 1 ≤ t ∧ K < ‖continuousCesaro T t y‖ / (e t * bernsteinRate g t)) ↔
    (∀ K : ℝ, ∃ t : ℝ, 1 ≤ t ∧
      K < ‖continuousCesaro T t y‖ / (e t * (bernsteinValue g ((1 / t : ℝ) : ℂ)).re)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
