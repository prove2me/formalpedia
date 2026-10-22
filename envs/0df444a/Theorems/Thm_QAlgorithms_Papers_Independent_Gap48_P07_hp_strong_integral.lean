-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_hp_strong_integral
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.hp_strong_integral
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:11:53.50998+00:00
-- url     : https://prove2.me/theorems/b202f7fb-e60f-4c4e-97b4-8877114da8e5
-- title:
--   §2.2, equations (2.2): elementary HP strong integral
-- statement:
--   Let $X$ be a complex Banach space and $(T(s))_{s\ge0}$ a bounded strongly continuous semigroup, with negative generator $A$ constructed from $T$ and $M=\sup_{s\ge0}\|T(s)\|$. Let $A_+^1$ consist of Laplace transforms of finite complex Radon measures on $[0,\infty)$, with total variation norm. The same-semigroup elementary calculus $\rho_T$ is a continuous unital complex algebra homomorphism into $\mathcal L(X)$, and for every representing measure $\mu$ and every $x\in X$,
--   $$\rho_T(\mathcal L\mu)x=\int_{[0,\infty)}T(s)x\,\mu(ds),\qquad \|\rho_T(f)\|\le M\|f\|_{A_+^1}.$$
--   All vector integrals exist and are independent of the representing finite positive measure and complex density. Explicitly, $\rho_T(1)=I$, $\rho_T(f+g)=\rho_T(f)+\rho_T(g)$, $\rho_T(fg)=\rho_T(f)\rho_T(g)$ and $\rho_T(cf)=c\rho_T(f)$; also $\|(\rho_T(f)-\rho_T(g))x\|\le M\|f-g\|_{A_+^1}\|x\|$. This supplies the concrete bounded calculus needed before regularization.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 4, §2.2, equations (2.2): elementary HP strong integral

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

/-- PDF pp.4–5, (2.2): elementary HP homomorphism, continuity estimate, norm
bound, vectorwise integrability and representation independence on this T. -/
theorem hp_strong_integral (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) :
    (∀ f : ℂ → ℂ, LaplaceImage f → ∃ B : X →L[ℂ] X,
      (∀ x, hpEval T f x = B x) ∧ ‖B‖ ≤ semigroupBound T * laplaceNorm f ∧
      ∀ d, FiniteRep f d → ∀ x : X,
        Integrable (fun s => d.2 s • T (s : ℝ) x) d.1 ∧
        B x = ∫ s, d.2 s • T (s : ℝ) x ∂d.1) ∧
    (∀ x : X, hpEval T 1 x = x) ∧
    (∀ f g : ℂ → ℂ, LaplaceImage f → LaplaceImage g → ∀ x : X,
      hpEval T (f + g) x = hpEval T f x + hpEval T g x ∧
      hpEval T (f * g) x = hpEval T f (hpEval T g x) ∧
      ‖hpEval T f x - hpEval T g x‖ ≤ semigroupBound T * laplaceNorm (f - g) * ‖x‖) ∧
    (∀ c : ℂ, ∀ f : ℂ → ℂ, LaplaceImage f → ∀ x : X,
      hpEval T (c • f) x = c • hpEval T f x) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
