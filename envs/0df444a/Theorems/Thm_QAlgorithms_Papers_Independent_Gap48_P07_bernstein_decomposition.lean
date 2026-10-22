-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_bernstein_decomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.bernstein_decomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:16:09.332687+00:00
-- url     : https://prove2.me/theorems/a74a715d-3272-4e12-9339-5c539c4fbd55
-- title:
--   Lemma 2.5.
-- statement:
--   Let $g$ be any Bernstein function, including zero. There exist elementary Laplace symbols $g_1,g_2\in A_+^1(\mathbb C_+)$ such that
--   $$g(z)=g_1(z)+z g_2(z)\qquad(z>0).$$
--   No positivity or uniqueness of these summands is claimed. The decomposition supplies bounded Laplace constituents for regularizing Bernstein functions.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 9, Lemma 2.5.

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

/-- PDF p.9, Lemma 2.5: neither positivity nor uniqueness of summands is asserted. -/
theorem bernstein_decomposition (g : BernsteinData) :
    ∃ g1 g2 : ℂ → ℂ, LaplaceImage g1 ∧ LaplaceImage g2 ∧ ∀ z : ℝ, 0 < z →
      bernsteinValue g (z : ℂ) = g1 (z : ℂ) + (z : ℂ) * g2 (z : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
