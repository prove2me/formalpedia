-- Prove2me | Theorems.Thm_SYKCavity_lemma_40
-- name    : SYKCavity.lemma_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:19.158916+00:00
-- url     : https://prove2.me/theorems/2afbd9ab-a74c-40af-a9f9-eb0515d41a0f
-- title:
--   Lemma 40 — the positive scalar saddle exists, is unique, satisfies $\tfrac12e^{-\beta/4}\le G_*\le\tfrac12$ and $\|G_{*,\beta}-G_{*,\beta'}\|_\infty\le|\beta^2-\beta'^2|/16\pi$
-- statement:
--   For $\beta\ge0$ consider the SYK saddle equations (3.21), $\Sigma_*=\beta^2G_*^3$, $\hat G_*(n)=(-i\omega_n-\hat\Sigma_*(n))^{-1}$, $\omega_n=(2n+1)\pi$, among normalized positive spectral kernels $G_\mu(t)=\int\frac{\cosh(x(1/2-t))}{2\cosh(x/2)}\mu(dx)$, $\mu$ a probability measure on $[0,\infty)$.
--
--   1. For every $\beta\ge0$ there is exactly one solution $G_*=G_{\mu_{*,\beta}}$.
--   2. For $\beta>0$,
--   $$\int x^2\,\mu_{*,\beta}(dx)=\frac{\beta^2}4,\qquad\tfrac12e^{-\beta/4}\le G_*(t)\le\tfrac12\ \ (0\le t\le1),\qquad\int e^{x/(2\beta)}\mu_{*,\beta}(dx)\le1+\sqrt2.$$
--   3. At $\beta=0$, $\mu_{*,0}=\delta_0$.
--   4. On each compact temperature interval $[\beta_1,\beta_2]\subseteq[0,\infty)$ there are one complex neighbourhood $U$ of $[0,1]$ and one bound $M$ such that every $G_{*,\beta}$, $\beta\in[\beta_1,\beta_2]$, extends from $[0,1]$ to a holomorphic function on $U$ bounded by $M$.
--   5. For all $\beta,\beta'\ge0$,
--   $$\|G_{*,\beta}-G_{*,\beta'}\|_\infty\le\frac{|\beta^2-\beta'^2|}{16\pi}.$$
--
--   The saddle $G_*$ is the centre of the expansion behind the algorithm; these bounds make it computable and control the ladder kernel built from it.
--
--   **Formalization Note** The exponential moment is a lower Lebesgue integral, so it cannot hold through a junk value; `saddle β` is the chosen solution, which by part 1 is the unique one.
--
--   Differences from the source:
--   - encoding: a unique normalized positive spectral solution G* = G_{μ*,β} → ∃! probability measure μ on [0,∞) (as a measure on ℝ with μ(−∞,0) = 0) solving (3.21) with G = G_μ; reason: G_μ on [0,1] determines μ (a Laplace transform), so uniqueness of G and of μ coincide; the page names μ*,β
--   - encoding: ‖G*,β − G*,β′‖∞ (D.6) → the bound at every t ∈ [0,1]; reason: G* is defined on [0,1]; a bound at every point is the bound on the sup
--   - encoding: ∫ e^{x/(2β)} μ*,β(dx) ≤ 1 + √2 → lower Lebesgue integral of e^{x/(2β)}; reason: nonnegative integrand; avoids the Bochner junk value 0
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 40, p.88 ((D.4)–(D.6)); equations (3.21), p.23

import Mathlib
import Definitions.Def_SYKCavity_Saddle

open MeasureTheory

namespace SYKCavity

/-- **Lemma 40 (The positive scalar saddle)**, p.88 of A. Schmidhuber, A. Zlokapa, *Polynomial-time
algorithms for mean-field models up to the glass transition*, arXiv:2610.06807 (held version, sha256
25d817ba…cfc5).

1. For every `β ≥ 0` the saddle equations (3.21) have exactly one normalized positive spectral
   solution `G* = G_{μ*,β}` (exactly one probability measure `μ` on `[0, ∞)` solves them).
2. For `β > 0`: `∫ x² μ*,β(dx) = β²/4`, `½ e^{−β/4} ≤ G*(t) ≤ ½` on `[0, 1]` (D.4), and
   `∫ e^{x/(2β)} μ*,β(dx) ≤ 1 + √2` (D.5).
3. At `β = 0`, `μ*,0 = δ₀`.
4. For every compact temperature interval `[β₁, β₂] ⊆ [0, ∞)` there are one open neighbourhood `U` of
   `[0, 1]` in `ℂ` and one bound `M` such that for every `β` in the interval `G*` on `[0, 1]` extends
   to a holomorphic function on `U` bounded by `M`.
5. `sup_{t ∈ [0,1]} |G*,β(t) − G*,β′(t)| ≤ |β² − β′²| / (16π)` for all `β, β′ ≥ 0` (D.6).

**Formalization Note.** `saddle β` is the solution chosen by `Classical.choose`; by clause 1 it is
the unique one. The exponential moment (D.5) is a lower Lebesgue integral, so it is not satisfied
through a junk value. -/
theorem lemma_40 :
    (∀ β : ℝ, 0 ≤ β → ∃! μ : Measure ℝ, IsSaddle β μ) ∧
    (∀ β : ℝ, 0 < β →
      ∫ x, x ^ 2 ∂(saddle β) = β ^ 2 / 4 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 2 * Real.exp (-β / 4) ≤ Gstar β t ∧ Gstar β t ≤ 1 / 2) ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (x / (2 * β))) ∂(saddle β) ≤
        ENNReal.ofReal (1 + Real.sqrt 2)) ∧
    saddle 0 = Measure.dirac 0 ∧
    (∀ β₁ β₂ : ℝ, 0 ≤ β₁ → β₁ ≤ β₂ →
      ∃ U : Set ℂ, IsOpen U ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, (t : ℂ) ∈ U) ∧
        ∃ M : ℝ, ∀ β ∈ Set.Icc β₁ β₂, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧
          (∀ z ∈ U, ‖F z‖ ≤ M) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, F t = Gstar β t) ∧
    (∀ β β' : ℝ, 0 ≤ β → 0 ≤ β' → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |Gstar β t - Gstar β' t| ≤ |β ^ 2 - β' ^ 2| / (16 * Real.pi)) := by sorry

end SYKCavity
