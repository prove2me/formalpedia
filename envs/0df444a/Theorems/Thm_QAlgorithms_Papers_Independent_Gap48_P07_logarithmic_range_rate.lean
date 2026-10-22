-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_logarithmic_range_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.logarithmic_range_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:24:26.540611+00:00
-- url     : https://prove2.me/theorems/7020c128-18c0-4e0c-b791-2c507887049d
-- title:
--   §5, unnumbered logarithmic range rate
-- statement:
--   Let $g(z)=(z-1)/\log z$ for the principal logarithm, with removable values $g(1)=1$ and $g(0)=0$. It is a complete Bernstein function with coefficients $a=b=0$. Its rate is comparable to $1/\log t$: there are positive constants $c_0,c_1$ such that
--   $$\frac{c_0}{\log t}\le r[g](t)\le\frac{c_1}{\log t}\qquad(t\ge2).$$
--   For every bounded strongly continuous semigroup $T$ with negative generator $A$, $\|C_t(A)x\|=O(1/\log t)$ for each $x\in\operatorname{ran}g(A)$. If nonzero spectral points of $A$ accumulate at zero, every positive nonincreasing $\epsilon(t)\to0$ admits $y$ in that range with $\sup_{t\ge1}(\log t)\|C_t(A)y\|/\epsilon(t)=+\infty$. The fixed symbol and its representing data precede the semigroup. This is the logarithmic range example with its stated optimality.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 22, §5, unnumbered logarithmic range rate

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

/-- PDF p.22: logarithmic range rate, complete Bernstein symbol with a=b=0,
eventual comparison and spectral optimality. -/
theorem logarithmic_range_rate :
    ∃ g : BernsteinData, CompleteBernstein g ∧ g.a = 0 ∧ g.b = 0 ∧
      (∀ z : ℂ, 0 ≤ z.re → bernsteinValue g z = logarithmicRateSymbol z) ∧
      (∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧ ∀ t : ℝ, 2 ≤ t →
        c0 / Real.log t ≤ bernsteinRate g t ∧ bernsteinRate g t ≤ c1 / Real.log t) ∧
      ∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
        (T : ℝ → Y →L[ℂ] Y), BoundedC0 T →
        (∀ x ∈ graphRange (hpGraph T logarithmicRateSymbol),
          Asymptotics.IsBigO atTop (fun t => ‖continuousCesaro T t x‖) (fun t : ℝ => 1 / Real.log t)) ∧
        (SpectralAccumulation T → ∀ e : ℝ → ℝ, VanishingFactor e →
          ∃ y ∈ graphRange (hpGraph T logarithmicRateSymbol), ∀ K : ℝ,
            ∃ t : ℝ, 1 ≤ t ∧ K < Real.log t * ‖continuousCesaro T t y‖ / e t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
