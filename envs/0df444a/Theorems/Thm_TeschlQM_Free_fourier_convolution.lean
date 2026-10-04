-- Prove2me | Theorems.Thm_TeschlQM_Free_fourier_convolution
-- name    : TeschlQM.Free.fourier_convolution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T00:49:05.557996+00:00
-- url     : https://prove2.me/theorems/d8ae44c8-b7a3-46c1-9069-36d8e3524ade
-- title:
--   Lemma 7.7 — convolution on L¹(ℝⁿ), Young's inequality, (f ∗ g)^ = (2π)^{n/2} f̂ ĝ
-- statement:
--   For $f, g \in L^1(\mathbb R^n)$ the **convolution**
--   $$(f * g)(x) = \int_{\mathbb R^n} f(y) g(x - y)\, d^ny = \int_{\mathbb R^n} f(x - y) g(y)\, d^ny$$
--   is again in $L^1(\mathbb R^n)$, satisfies Young's inequality $\|f * g\|_1 \le \|f\|_1 \|g\|_1$, and its Fourier transform (normalization $\hat f(p) = (2\pi)^{-n/2}\int e^{-ipx} f(x)\,d^nx$) is
--   $$(f * g)^\wedge(p) = (2\pi)^{n/2} \hat f(p) \hat g(p).$$
--
--   The convolution formula is how the free time evolution is written as an integral operator.
--
--   **Formalization Note.** The convolution is the explicit integral $x \mapsto \int f(y) g(x-y)\,dy$; at the null set of $x$ where the integrand is not integrable the Bochner integral is $0$, which changes neither the $L^1$ norm nor the Fourier transform. The two expressions in (7.17) are asserted equal for every $x$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 165, Lemma 7.7

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

namespace TeschlQM.Free

open MeasureTheory

/-- Teschl, Lemma 7.7, p. 165: for `f, g ∈ L¹(ℝⁿ)` the convolution
`(f ∗ g)(x) = ∫ f(y) g(x - y) dⁿy = ∫ f(x - y) g(y) dⁿy` (7.17) is in `L¹(ℝⁿ)`, satisfies Young's
inequality `‖f ∗ g‖₁ ≤ ‖f‖₁ ‖g‖₁` (7.18), and `(f ∗ g)^(p) = (2π)^{n/2} f̂(p) ĝ(p)` (7.19) with
Teschl's normalization (7.3). -/
theorem fourier_convolution (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∀ x, ∫ y, f y * g (x - y) = ∫ y, f (x - y) * g y) ∧
      Integrable (fun x => ∫ y, f y * g (x - y)) volume ∧
      ∫ x, ‖∫ y, f y * g (x - y)‖ ≤ (∫ x, ‖f x‖) * ∫ x, ‖g x‖ ∧
      fourier n (fun x => ∫ y, f y * g (x - y)) =
        fun p => (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * fourier n f p * fourier n g p := by sorry

end TeschlQM.Free
