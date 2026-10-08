-- Prove2me | Theorems.Thm_SAARate_Polyhedral_lemma_2_4_a
-- name    : SAARate.Polyhedral.lemma_2_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:29.312964+00:00
-- url     : https://prove2.me/theorems/69bdb93b-0cd6-49d4-b2c4-6b60178900f6
-- title:
--   Lemma 2.4 (a), p. 6 — finitely many points z_k carry every subdifferential of f and of f̂_N
-- statement:
--   Let $\Omega$ be finite, let $P$ be a probability measure on $\Omega$, and suppose every $h(\cdot,\omega)$, $\omega\in\Omega$, is piecewise linear and convex on $\mathbb R^m$. Write $f(x)=\mathbb E_P h(x,\omega)$ and, for a sample path $s=(\omega^1,\omega^2,\dots)$ in $\Omega$, $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$. Let $\partial g(x)$ be the subdifferential of a convex function $g$ at $x$.
--
--   Then there are finitely many points $z_1,\dots,z_r\in\mathbb R^m$, chosen independently of the sample, such that for every $x\in\mathbb R^m$ there is $k\in\{1,\dots,r\}$ with
--   $$
--   \partial f(x)=\partial f(z_k)\qquad\text{and}\qquad \partial\hat f_N(x)=\partial\hat f_N(z_k)\ \text{ for every sample path and every } N.
--   $$
--
--   This reduces questions about all subdifferentials of the true and the sample average functions to finitely many points; it is the source of the uniform convergence in Lemma 2.4 (b).
--
--   **Formalization Note** The statement assumes that every scenario has positive probability, $P\{\omega\}>0$ for all $\omega\in\Omega$, which is how p. 3 takes $\Omega=\{\omega_1,\dots,\omega_K\}$ to be the support of $P$. Without it the claim fails for sample paths visiting a null scenario whose $h(\cdot,\omega)$ has a kink where $f$ is affine. The subdifferential is the published `ShorNonsmooth.Subdiff.subdifferential` with domain $\mathbb R^m$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 6, Lemma 2.4 (a); p. 3, (2.1) for the finite support

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

open MeasureTheory ProbabilityTheory ShorNonsmooth.Subdiff

namespace SAARate.Polyhedral

/-- Lemma 2.4 (a), p. 6: under (i) `Ω` finite and (ii) every `h(·, ω)` piecewise linear and
convex, there are finitely many points `z_1, …, z_r`, independent of the sample, such that every
`x` has a `k` with `∂f(x) = ∂f(z_k)` and `∂f̂_N(x) = ∂f̂_N(z_k)` for every realization of the
sample. `hP` (every scenario has positive mass, p. 3) is a disclosed pin. -/
theorem lemma_2_4_a {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : ∀ ω, P {ω} ≠ 0)
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω)) :
    ∃ (r : ℕ) (z : Fin r → SAARate.Sharp.E m), ∀ x : SAARate.Sharp.E m, ∃ k : Fin r,
      subdifferential Set.univ (SAARate.Sharp.expectedObj P h) x =
          subdifferential Set.univ (SAARate.Sharp.expectedObj P h) (z k) ∧
        ∀ (s : ℕ → Ω) (N : ℕ),
          subdifferential Set.univ (SAARate.Sharp.saaObj h s N) x =
            subdifferential Set.univ (SAARate.Sharp.saaObj h s N) (z k) := by sorry

end SAARate.Polyhedral
