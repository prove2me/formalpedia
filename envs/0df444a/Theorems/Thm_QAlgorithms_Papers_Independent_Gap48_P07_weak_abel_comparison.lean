-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_weak_abel_comparison
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.weak_abel_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:15:39.115204+00:00
-- url     : https://prove2.me/theorems/e69350c1-f6a3-47c1-aa94-54644cf9dbae
-- title:
--   §2.2, unnumbered comparison of weak summability
-- statement:
--   For a bounded strongly continuous semigroup $T$ on a complex Banach space and a Laplace-transformable complex Radon measure $\mu$, improper weak convergence of $\int_{[0,r]}T(s)x\,\mu(ds)$ to $y$ as $r\to\infty$ implies weak Abel convergence of the corresponding damped integral to the same $y$. The implication is strict: for every real $a\ne0$ and every nonzero vector $x$, the multiplication semigroup $T(s)x=e^{ias}x$, with Lebesgue measure, satisfies
--   $$\lim_{\alpha\downarrow0}\int_0^\infty e^{-\alpha s}e^{ias}x\,ds=(-ia)^{-1}x,\qquad \int_0^r e^{ias}x\,ds=\frac{e^{iar}-1}{ia}x.$$
--   The damped integrals are genuine, and the primitives have no weak limit. This supplies an explicit strictness witness, including its Abel value and the sign of its primitive.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 7, §2.2, unnumbered comparison of weak summability

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

/-- PDF p.7: improper weak summability implies Abel summability, strictly.
The oscillatory example is for every nonzero vector and every a≠0. -/
theorem weak_abel_comparison :
    (∀ (T : ℝ → X →L[ℂ] X), BoundedC0 T → ∀ (m : LaplaceRadon) (x y : X),
      WeakImproper T m x y → WeakAbel T m x y) ∧
    (∀ a : ℝ, a ≠ 0 → ∀ x : X, x ≠ 0 →
      (∀ alpha : ℝ, 0 < alpha → IntegrableOn
        (fun s : ℝ => Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x)
        (Ici 0)) ∧
      (∀ l : X →L[ℂ] ℂ, Tendsto
        (fun alpha : ℝ => l (∫ s in Ici (0 : ℝ),
          Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x))
        (𝓝[>] 0) (𝓝 (l ((-Complex.I * (a : ℂ))⁻¹ • x)))) ∧
      (∀ r : ℝ, 0 ≤ r → (∫ s in Icc (0 : ℝ) r,
        Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x) =
        ((Complex.exp (Complex.I * (a : ℂ) * (r : ℂ)) - 1) / (Complex.I * (a : ℂ))) • x) ∧
      ¬ ∃ y : X, ∀ l : X →L[ℂ] ℂ, Tendsto
        (fun r : ℝ => l (∫ s in Icc (0 : ℝ) r,
          Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x)) atTop (𝓝 (l y))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
