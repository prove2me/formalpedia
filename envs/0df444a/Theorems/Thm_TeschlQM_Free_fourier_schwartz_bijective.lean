-- Prove2me | Theorems.Thm_TeschlQM_Free_fourier_schwartz_bijective
-- name    : TeschlQM.Free.fourier_schwartz_bijective
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T00:25:26.367049+00:00
-- url     : https://prove2.me/theorems/00c811b5-0d46-4198-9800-6b0b8683afd7
-- title:
--   Theorem 7.4 — F is a bijection of 𝒮(ℝⁿ) with inverse (7.8); F²f(x) = f(−x), F⁴ = 𝕀
-- statement:
--   Let $\mathcal S(\mathbb R^n)$ be the Schwartz space of smooth functions all of whose derivatives decay faster than any polynomial. The Fourier transform $\hat f(p) = (2\pi)^{-n/2}\int e^{-ipx} f(x)\,d^nx$ maps $\mathcal S(\mathbb R^n)$ bijectively onto itself, and its inverse is
--   $$\mathcal F^{-1}(g)(x) = \check g(x) = \frac{1}{(2\pi)^{n/2}}\int_{\mathbb R^n} e^{ipx} g(p)\, d^np .$$
--   Moreover $\mathcal F^2(f)(x) = f(-x)$, and hence $\mathcal F^4 = \mathbb I$.
--
--   This is the Fourier inversion theorem on Schwartz space, from which the unitary $L^2$ transform is obtained.
--
--   **Formalization Note.** Schwartz functions are Mathlib's `SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ`. The statement asserts: $\hat f$ is (the coercion of) a Schwartz function for every Schwartz $f$; every Schwartz $g$ is some $\hat f$; `fourierInv` inverts `fourier` on both sides on $\mathcal S$; $\mathcal F^2 f(x) = f(-x)$ for all $x$; and $\mathcal F^4 f = f$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 163, Theorem 7.4

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

namespace TeschlQM.Free

/-- Teschl, Theorem 7.4, p. 163: the Fourier transform (Teschl's normalization (7.3)) is a bijection
of the Schwartz space `𝒮(ℝⁿ)` onto itself, its inverse is the transform `F⁻¹` of (7.8)
(`fourierInv`), `F²(f)(x) = f(-x)`, and hence `F⁴ = I`. -/
theorem fourier_schwartz_bijective (n : ℕ) :
    (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ⇑g = fourier n f) ∧
      (∀ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, fourier n f = ⇑g) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        fourierInv n (fourier n f) = ⇑f ∧ fourier n (fourierInv n f) = ⇑f) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, fourier n (fourier n f) x = f (-x)) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        fourier n (fourier n (fourier n (fourier n f))) = ⇑f) := by sorry

end TeschlQM.Free
