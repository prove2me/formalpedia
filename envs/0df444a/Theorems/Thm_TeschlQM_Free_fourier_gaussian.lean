-- Prove2me | Theorems.Thm_TeschlQM_Free_fourier_gaussian
-- name    : TeschlQM.Free.fourier_gaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T00:18:56.725135+00:00
-- url     : https://prove2.me/theorems/a3cdb05c-fc59-49ad-9610-c14e5245ba16
-- title:
--   Lemma 7.3 — Fourier transform of the Gaussian e^{−zx²/2}, Re z > 0
-- statement:
--   Let $z \in \mathbb C$ with $\operatorname{Re}(z) > 0$. Then $e^{-zx^2/2}$ is a Schwartz function on $\mathbb R^n$, and its Fourier transform, in the normalization $\hat f(p) = (2\pi)^{-n/2}\int e^{-ipx} f(x)\,d^nx$, is
--   $$\mathcal F\big(e^{-zx^2/2}\big)(p) = \frac{1}{z^{n/2}}\, e^{-p^2/(2z)} .$$
--   Here $z^{n/2}$ means $(\sqrt z)^n$, where the branch cut of the root is chosen along the negative real axis.
--
--   The Gaussian is the explicit function from which the Fourier inversion formula and the kernel of the free time evolution are derived.
--
--   **Formalization Note.** $\sqrt z$ is `z ^ (1/2 : ℂ)`, Mathlib's principal branch of `cpow`, whose cut is the negative real axis; $\operatorname{Re} z > 0$ keeps $z$ off it. The Schwartz property is stated as the existence of a `SchwartzMap` equal to the Gaussian pointwise.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 162, Lemma 7.3

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

namespace TeschlQM.Free

open MeasureTheory

/-- Teschl, Lemma 7.3, p. 162: for `Re z > 0` the Gaussian `e^{-zx²/2}` is a Schwartz function on
`ℝⁿ` and its Fourier transform (Teschl's normalization (7.3)) is
`F(e^{-zx²/2})(p) = z^{-n/2} e^{-p²/(2z)}`, where `z^{n/2}` means `(√z)ⁿ` with the principal
branch of the square root (branch cut along the negative real axis), here `z ^ (1/2 : ℂ)`. -/
theorem fourier_gaussian (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    (∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∀ x, φ x = Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) ∧
      fourier n (fun x => Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) =
        fun p => ((z ^ (1 / 2 : ℂ)) ^ n)⁻¹ * Complex.exp (-((‖p‖ ^ 2 : ℝ) : ℂ) / (2 * z)) := by sorry

end TeschlQM.Free
